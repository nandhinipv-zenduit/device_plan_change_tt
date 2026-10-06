r"""
Geotab + Zenduit plan-change check  (single file: python main.py)

For each source (Geotab, Zenduit) compares the saved baseline table against
the live Zoho Analytics view and emails every serial number whose plan
differs. One email per run, Geotab section first, then Zenduit.

    pip install requests python-dotenv
    python main.py                 # the daily check
    python main.py get-token       # one-off: mint the Google refresh token (Drive + Gmail send)
    python main.py check-token     # one-off: test a refresh token against the Drive folder
    python main.py zoho-token CODE # one-off: mint the Zoho CRM refresh token from a grant code

THE FILES ALWAYS LIVE IN GOOGLE DRIVE
    My Drive\Device_discrepancy
        Geotab_Devices.csv                      <- Geotab baseline (= previous run's table)
        Zenduit_Devices.csv                     <- Zenduit baseline
        plan_changes_geotab_<timestamp>.csv     <- one report per source per run
        plan_changes_zenduit_<timestamp>.csv
        compare_plans.log                       <- appended every run
        baseline_backups\                       <- gzipped copies of each previous baseline

TWO WAYS TO RUN IT (STORAGE in .env / workflow)

  * STORAGE=gdrive  — GitHub Actions (see .github/workflows/plan-check.yml and
    SETUP.md). The runner has no Drive mount, so the Drive section below downloads the
    baselines and log from the Drive folder into a scratch folder first, the
    run happens there unchanged, and afterwards everything the run changed or
    created is uploaded back. Baselines are replaced in place, so the Drive
    files keep their ids, owner and sharing. Needs GDRIVE_CLIENT_ID,
    GDRIVE_CLIENT_SECRET, GDRIVE_REFRESH_TOKEN and GDRIVE_FOLDER_ID.

  * STORAGE=local (default) — a PC where Google Drive is mounted.
    DISCREPANCY_DIR defaults to G:\My Drive\Device_discrepancy.

    Never run both on a schedule at once: each run rolls the shared baseline
    forward, so the second one that day would find nothing to report.

    A baseline whose name ends in .gz is read and written gzipped (optional;
    the defaults are plain CSV, as the folder has always held).

SOURCES
    Both views live in Analytics workspace 953790000013364003:
        Geotab   view 953790000054827102   serial='serial…', plan='activeDevicePlan_name'
        Zenduit  view 953790000054827175   serial='serial_number', plan='Plan'
    Column names are matched by the lists in SOURCES below, with a fuzzy
    fallback, and the columns actually picked are written to the log.

NEVER-ACTIVATED DEVICES ARE EXCLUDED
    A device with no plan on either side has never been provisioned, so it
    appearing in or dropping out of the table is not a billing change. Those are
    filtered out; the run log says how many. Terminations (a device that HAD a
    plan and lost it) are still reported — that device was activated.
    Pass --include-never-activated to see them anyway.

WHAT A RUN DOES, IN ORDER
    1. Pull the current table for every source from Zoho Analytics.
    2. Compare each against its baseline CSV.
    3. Write plan_changes_<source>_<timestamp>.csv for each source with changes.
    4. Send ONE email with a section (and attachment) per source.
    5. ONLY THEN: back up each old baseline (gzipped) and replace it with the
       new data, so the next run compares against today.

    Step 5 is last on purpose. If the email fails the script stops before it,
    leaving every baseline alone — otherwise a failed send would erase changes
    nobody had been told about, and no later run would ever report them.

    A source whose baseline does not exist yet gets one written at step 5 and
    is reported in the email as "baseline created, nothing to compare yet",
    so adding Zenduit does not need a separate first-run step.

    python main.py                        # the above
    python main.py --no-update-baseline   # stop after step 4
    python main.py --only geotab          # run a single source
    python main.py --only zenduit

.env (next to this script) or environment:
    ZOHO_ORG_ID, ZOHO_CLIENT_ID_ANALYTICS, ZOHO_CLIENT_SECRET_ANALYTICS,
    ZOHO_CLIENT_REFRESH_TOKEN_ANALYTICS,
    EMAIL_FROM, EMAIL_TO, MAIL_VIA (gmail_api | smtp)
    SMTP_HOST, SMTP_PORT, SMTP_USERNAME, SMTP_PASSWORD   (smtp mode only)
    STORAGE (local | gdrive), DISCREPANCY_DIR (local mode), WORK_DIR (gdrive mode)
    GDRIVE_CLIENT_ID, GDRIVE_CLIENT_SECRET, GDRIVE_REFRESH_TOKEN, GDRIVE_FOLDER_ID
    GEOTAB_BASELINE_NAME, ZENDUIT_BASELINE_NAME (optional; end in .gz to gzip)
    GEOTAB_VIEW_ID, ZENDUIT_VIEW_ID (optional, default to the IDs above)
    KEEP_BACKUPS (optional; 0 disables baseline_backups/), KEEP_REPORTS
"""
import base64
import collections
import csv
import datetime
import html as html_mod
import gzip
import http.server
import io
import json
import os
import re
import secrets
import shutil
import smtplib
import sys
import threading
import time
import traceback
import urllib.parse
import webbrowser
from email.mime.application import MIMEApplication
from email.mime.multipart import MIMEMultipart
from email.mime.text import MIMEText

import requests

try:
    from dotenv import load_dotenv
    load_dotenv()
except ImportError:
    pass


def env(name, default=""):
    v = os.getenv(name)
    return default if v is None or not v.strip() else v.strip()


STORAGE = env("STORAGE", "local").lower()          # local | gdrive
if STORAGE == "gdrive":
    # Scratch folder on the runner. The Drive sync fills it before the run and
    # uploads from it afterwards; everything else in this file just sees a
    # normal local folder.
    DISCREPANCY_DIR = env("WORK_DIR", os.path.join(os.getcwd(), "work"))
    os.makedirs(DISCREPANCY_DIR, exist_ok=True)
elif STORAGE == "local":
    DISCREPANCY_DIR = env("DISCREPANCY_DIR", r"G:\My Drive\Device_discrepancy")
else:
    sys.exit(f"STORAGE must be 'local' or 'gdrive', not '{STORAGE}'")
LOG_NAME = "compare_plans.log"
LOG_PATH = os.path.join(DISCREPANCY_DIR, LOG_NAME)
BACKUP_SUBDIR = "baseline_backups"

GDRIVE_FOLDER_ID = env("GDRIVE_FOLDER_ID")
GDRIVE_CLIENT_ID = env("GDRIVE_CLIENT_ID")
GDRIVE_CLIENT_SECRET = env("GDRIVE_CLIENT_SECRET")
GDRIVE_REFRESH_TOKEN = env("GDRIVE_REFRESH_TOKEN")
# 0 (default): only the two baseline tables are read from / written to Drive.
#              Reports, log and backups stay on the GitHub run as artifacts.
# 1:           mirror reports, log and backups to Drive too (old PC layout).
GDRIVE_SYNC_EXTRAS = env("GDRIVE_SYNC_EXTRAS", "0") == "1"

# How many old baselines to keep PER SOURCE in baseline_backups/. Backups are
# gzipped, but the exports are large and 20 copies of each is plenty, so they
# are pruned oldest-first rather than left to fill the Drive. 0 = no backups.
KEEP_BACKUPS = int(env("KEEP_BACKUPS", "20"))
KEEP_REPORTS = int(env("KEEP_REPORTS", "200"))      # per source

WORKSPACE_ID = env("ZOHO_ANALYTICS_WORKSPACE_ID", "953790000013364003")

# Zoho CRM: both device tables carry the CRM Account record id, so the customer
# name in the email links straight to the account page without any CRM lookup.
CRM_ORG = env("CRM_ORG_ID", "3130230")                 # crm.zoho.com/crm/org<this>/...
CRM_ACCOUNT_URL = env("CRM_ACCOUNT_URL", f"https://crm.zoho.com/crm/org{CRM_ORG}/tab/Accounts/{{crm_id}}")

# Device page links. Templates with placeholders filled from the row:
#   {serial} {device_id} {company_id} {database} {account} {crm_id}
# Leave blank for plain-text serials. Set in the workflow (GEOTAB_DEVICE_URL,
# ZENDUIT_DEVICE_URL) once the portal URL pattern is known.
GEOTAB_DEVICE_URL = env("GEOTAB_DEVICE_URL", "")
ZENDUIT_DEVICE_URL = env("ZENDUIT_DEVICE_URL", "")

# Zoho CRM cancellation requests. Each terminated device is looked up in the
# CRM "Cancellations" module (custom module CustomModule3) and its "Cancelled
# Items" subform (Subform_2), where the serials are typed in. Needs a Zoho
# refresh token with CRM read scopes (ZohoCRM.modules.READ, ZohoCRM.coql.READ);
# `python main.py zoho-token <grant code>` mints one. Without the token the
# lookup is skipped and the email says so.
CRM_LOOKBACK_DAYS = int(env("CRM_LOOKBACK_DAYS", "180"))
CRM_API = env("ZOHO_CRM_API", "https://www.zohoapis.com/crm/v8")
CRM_CANCELLATION_URL = env("CRM_CANCELLATION_URL",
                           f"https://crm.zoho.com/crm/org{CRM_ORG}/tab/CustomModule3/{{id}}")

# One entry per device family. Order here is the order of the email sections
# and of everything in the log: Geotab first, Zenduit second.
#
#   key            short id used in file names and --only
#   label          what the email shows
#   view_id        Analytics view to export
#   baseline       baseline CSV name inside DISCREPANCY_DIR
#   id_cols        (optional) column that uniquely identifies a device ROW.
#                  When absent the serial number is the identity.
#   serial_cols    column names tried in order for the serial number shown
#                  in the email; the first non-blank value wins per row
#   plan_cols      exact column names tried first for the plan
#   customer_cols  exact column names tried first for the customer (optional)
#   crm_id_cols    column holding the Zoho CRM Account id (optional)
#   alt_id_cols    other identifiers (SIM, modem serial...) matched against
#                  CRM cancellation requests besides the serial
#   blank_plans    plan values that mean "no plan" (lower-cased)
#   terminated_plans  plan values that mean the device was terminated
#   device_url     link template for the serial (see above)
#   url_fields     placeholder name -> column, for the device_url template
#   columns        extra columns shown in the email/xlsx: (label, [cols], kind)
#                  kind: "text" | "date" | "datamb" (megabytes -> GB/MB)
#
# If none of the exact names exist, find_col falls back to a fuzzy match
# (any column containing every word in the fuzzy list), so a renamed column in
# Analytics does not kill the run — the log says which column got picked.
SOURCES = [
    {
        "key": "geotab",
        "label": "Geotab",
        "view_id": env("GEOTAB_VIEW_ID", "953790000054827102"),
        "baseline": env("GEOTAB_BASELINE_NAME", "Geotab_Devices.csv"),
        "serial_cols": ["device_serialNumber", "serial", "Serial", "serialNumber", "Serial Number"],
        "plan_cols": ["activeDevicePlan_name"],
        "customer_cols": ["userContact_userCompany_name", "Customer", "Customer Name"],
        "crm_id_cols": ["userContact_userCompany_partnerCustomerId"],
        # other identifiers a cancellation request might quote for this device
        "alt_id_cols": ["device_modemSerialNo", "simCardNumber", "Hardware ID"],
        "blank_plans": {""},
        "terminated_plans": set(),
        "device_url": GEOTAB_DEVICE_URL,
        "url_fields": {"device_id": "device_id", "database": "OwnerDatabaseName",
                       "account": "account_accountId"},
        "columns": [
            ("Reseller Acct", ["account_accountId"], "text"),
            ("Device Type", ["device_deviceType_name"], "text"),
            ("Database", ["OwnerDatabaseName", "latestDeviceDatabase_databaseName"], "text"),
            ("Billing Plan", ["Active Billing Plan"], "text"),
            ("Billing Status", ["Billing Status"], "text"),
            ("Last Communicate", ["latestDeviceDatabase_statusDate"], "date"),
            ("Date Added", ["startDate", "firstDeviceActivationDate"], "date"),
        ],
    },
    {
        # The Zenduit table (checked against the real export, Oct 2026):
        #   Device_Id      unique per row -> the identity. The same serial can
        #                  appear under several companies (demo/test accounts),
        #                  and ~6,000 rows carry a plan but no serial at all, so
        #                  keying on serial would merge or drop real devices.
        #   serial_number  the serial to show; 'Serial' is the fallback
        #   Plan           e.g. 'ZenduONE - Enterprise', 'Terminated',
        #                  'Suspended'. 'None' and '' both mean no plan.
        #   Company_Name   the customer;  AccountId = Zoho CRM account id
        "key": "zenduit",
        "label": "Zenduit",
        "view_id": env("ZENDUIT_VIEW_ID", "953790000054827175"),
        "baseline": env("ZENDUIT_BASELINE_NAME", "Zenduit_Devices.csv"),
        "id_cols": ["Device_Id", "device_id", "DeviceId"],
        "serial_cols": ["serial_number", "Serial", "Serial Number", "serial", "serialNumber"],
        "plan_cols": ["Plan", "plan", "plan_name", "Plan Name"],
        "customer_cols": ["Company_Name", "Customer", "Customer Name", "customer",
                          "customer_name", "Company", "company", "company_name"],
        "crm_id_cols": ["AccountId"],
        "alt_id_cols": ["SIM", "Serial", "Third_Party_Serial", "Device_Name"],
        "blank_plans": {"", "none", "null"},
        "terminated_plans": {"terminated"},
        "device_url": ZENDUIT_DEVICE_URL,
        "url_fields": {"device_id": "Device_Id", "company_id": "CompanyId",
                       "account": "AccountId"},
        "columns": [
            ("Reseller", ["Reseller_Name"], "text"),
            ("Tracker Type", ["Tracker_type"], "text"),
            ("Device Name", ["Device_Name"], "text"),
            ("Data Plan", ["Data_Plan"], "datamb"),
            ("Billing Plan", ["Billing_Plan"], "text"),
            ("Last Communicate", ["Last_active"], "date"),
            ("Date Added", ["CreationDate", "Activation_Date"], "date"),
        ],
    },
]

ORG_ID = env("ZOHO_ORG_ID", "67409019")
A_ID = env("ZOHO_CLIENT_ID_ANALYTICS")
A_SECRET = env("ZOHO_CLIENT_SECRET_ANALYTICS")
A_REFRESH = env("ZOHO_CLIENT_REFRESH_TOKEN_ANALYTICS")
# CRM token: same client as Analytics unless a separate one is given.
CRM_ID = env("ZOHO_CLIENT_ID_CRM", A_ID)
CRM_SECRET = env("ZOHO_CLIENT_SECRET_CRM", A_SECRET)
CRM_REFRESH = env("ZOHO_CLIENT_REFRESH_TOKEN_CRM")

SMTP_HOST = env("SMTP_HOST", "smtp.gmail.com")
SMTP_PORT = int(env("SMTP_PORT", "587"))
# The password comes ONLY from the environment (.env locally, a repository
# secret on GitHub). It must never be written into this file: the repo holds
# customer data and the script, and a leaked Gmail app password is a full
# mailbox login.
SMTP_USER = env("SMTP_USERNAME", "nandhinipv@zenduit.com")
SMTP_PASS = env("SMTP_PASSWORD")
MAIL_FROM = env("EMAIL_FROM", SMTP_USER)
# A list, always. ", ".join("a@b.com") would spell the address out letter by letter.
MAIL_TO = [a.strip() for a in env("EMAIL_TO", "billing@gofleet.com").split(",") if a.strip()]
# Failure alerts go here instead of to billing (whose mailbox raises a ticket for every mail).
FAILURE_TO = [a.strip() for a in env("FAILURE_EMAIL_TO", SMTP_USER).split(",") if a.strip()]
# How to send: gmail_api (HTTPS, uses the Google refresh token's gmail.send
# permission) or smtp (app password). Defaults to the API whenever a Google
# token is configured, because Gmail refuses SMTP logins from GitHub runners.
MAIL_VIA = env("MAIL_VIA", "gmail_api" if GDRIVE_REFRESH_TOKEN else "smtp").lower()

REPORT_TZ = env("REPORT_TZ", "America/Toronto")   # timezone for dates shown in the email


def say(msg):
    """Print AND append to a log file in the Drive folder.

    A scheduled task has nowhere to print to, so without the file there is no
    way to find out why a run did nothing. The log is in the synced folder on
    purpose: you can read it from any machine.
    """
    line = f"{time.strftime('%Y-%m-%d %H:%M:%S')}  {msg}"
    print(line, flush=True)
    try:
        os.makedirs(DISCREPANCY_DIR, exist_ok=True)
        with open(LOG_PATH, "a", encoding="utf-8") as fh:
            fh.write(line + "\n")
    except OSError:
        pass  # never let logging break the run


def die(msg):
    say("ERROR: " + msg.replace("\n", "\n       "))
    sys.exit(1)


# ---------------------------------------------------------------- reading CSVs

def find_col(fieldnames, candidates, fuzzy, label, required=True):
    for c in candidates:
        if c in fieldnames:
            return c
    for name in fieldnames:
        if all(t in (name or "").lower() for t in fuzzy):
            return name
    if required:
        die(f"no '{label}' column. Columns found: {fieldnames}")
    return ""


def to_plan_map(text, source, label):
    """device id -> {plan, customer, serial, crm_id, fields{label: value}, url{...}}

    The id is the serial number unless the source names an id column (Zenduit:
    Device_Id). The serial is what the email shows; when a row has no serial
    in any of the serial columns the id itself is shown instead."""
    rows = list(csv.DictReader(io.StringIO(text)))
    if not rows:
        die(f"{label} has no rows.")
    cols = list(rows[0].keys())
    s_cols = [c for c in source["serial_cols"] if c in cols]
    if not s_cols:
        s_cols = [find_col(cols, [], ["serial"], "serial number")]
    id_col = ""
    if source.get("id_cols"):
        id_col = find_col(cols, source["id_cols"], ["device", "id"], "device id", required=False)
        if not id_col:
            say(f"{label}: WARNING no id column {source['id_cols']} - keying on serial instead")
    p_col = find_col(cols, source["plan_cols"], ["plan"], "plan")
    c_col = (find_col(cols, source["customer_cols"], ["customer"], "customer", required=False)
             or find_col(cols, [], ["company"], "customer", required=False))
    crm_col = next((c for c in source.get("crm_id_cols", []) if c in cols), "")
    extra = [(lab, next((c for c in cands if c in cols), ""), kind)
             for lab, cands, kind in source.get("columns", [])]
    url_fields = {k: v for k, v in source.get("url_fields", {}).items() if v in cols}
    alt_cols = [c for c in source.get("alt_id_cols", []) if c in cols]
    blank_plans = source.get("blank_plans") or {""}

    def val(r, c):
        # Analytics exports some text HTML-encoded ("Rubber &amp; Plastic"); undo that.
        return html_mod.unescape(str(r.get(c) or "")).strip() if c else ""

    out, dropped, dups = {}, 0, 0
    for r in rows:
        serial = next((val(r, c) for c in s_cols if val(r, c)), "")
        key = val(r, id_col) if id_col else serial
        if not key:
            dropped += 1                      # no identity at all: cannot be tracked
            continue
        plan = val(r, p_col)
        if plan.lower() in blank_plans:
            plan = ""
        if key in out:
            dups += 1
        out[key] = {
            "plan": plan,
            "customer": val(r, c_col),
            "serial": serial or key,
            "has_serial": bool(serial),
            "crm_id": val(r, crm_col),
            "alt_ids": [val(r, c) for c in alt_cols if val(r, c)],
            "fields": {lab: fmt_field(val(r, c), kind) for lab, c, kind in extra},
            "url": {**{k: val(r, c) for k, c in url_fields.items()},
                    "serial": serial or key, "crm_id": val(r, crm_col)},
        }
    say(f"{label}: {len(out)} devices  (id='{id_col or s_cols[0]}', serial='{'/'.join(s_cols)}', "
        f"plan='{p_col}', customer='{c_col or '-'}', crm='{crm_col or '-'}')")
    if dropped:
        say(f"{label}: {dropped} row(s) skipped - no id and no serial")
    if dups:
        say(f"{label}: {dups} duplicate id(s) - last row wins")
    return out


def fmt_field(value, kind):
    if kind == "date":
        return fmt_date(value)
    if kind == "datamb":
        return fmt_data_mb(value)
    return value


def fmt_data_mb(value):
    """Data plan given in MB: 2448 -> '2.39 GB', 30 -> '30 MB', -1/blank -> ''."""
    try:
        mb = float(str(value).strip())
    except (TypeError, ValueError):
        return (value or "").strip()
    if mb <= 0:
        return ""
    return f"{mb / 1024:.2f} GB" if mb >= 1000 else f"{mb:g} MB"


def fmt_date(value):
    """'2026-10-05T04:16:38.000Z' / '05 Oct 2026 00:00:00' / '2025-11-21' -> 'Oct 05, 2026 00:16 EDT'.
    Times are shown in America/Toronto. Anything unparseable is returned as-is."""
    v = (value or "").strip()
    if not v or v.startswith("0001-01-01"):
        return ""
    dt = None
    for fmt in ("%Y-%m-%dT%H:%M:%S.%fZ", "%Y-%m-%dT%H:%M:%SZ", "%Y-%m-%dT%H:%M:%S",
                "%Y-%m-%d %H:%M:%S", "%d %b %Y %H:%M:%S", "%Y-%m-%d"):
        try:
            dt = datetime.datetime.strptime(v, fmt)
            break
        except ValueError:
            continue
    if dt is None:
        return v
    if fmt == "%Y-%m-%d" or (dt.hour, dt.minute, dt.second) == (0, 0, 0):
        # date-only values (Last_active comes as "05 Oct 2026 00:00:00"): no
        # timezone shift, or midnight UTC would display as the previous evening
        return dt.strftime("%b %d, %Y")
    try:
        from zoneinfo import ZoneInfo
        dt = dt.replace(tzinfo=datetime.timezone.utc).astimezone(ZoneInfo(REPORT_TZ))
        return dt.strftime("%b %d, %Y %H:%M %Z")
    except Exception:
        return dt.strftime("%b %d, %Y %H:%M UTC")


def strip_bom(text):
    return text[1:] if text and text[0] == "\ufeff" else text


def read_local_csv(path):
    raw = open(path, "rb").read()
    if raw[:2] == b"\x1f\x8b":
        raw = gzip.decompress(raw)
    return strip_bom(raw.decode("utf-8", "replace"))


# ------------------------------------------------------------- Analytics

def analytics_token():
    if not (A_ID and A_SECRET and A_REFRESH):
        die("missing Analytics credentials (ZOHO_CLIENT_ID_ANALYTICS, "
            "ZOHO_CLIENT_SECRET_ANALYTICS, ZOHO_CLIENT_REFRESH_TOKEN_ANALYTICS) in .env")
    r = requests.post("https://accounts.zoho.com/oauth/v2/token", data={
        "grant_type": "refresh_token", "client_id": A_ID,
        "client_secret": A_SECRET, "refresh_token": A_REFRESH}, timeout=60)
    r.raise_for_status()
    token = r.json().get("access_token")
    if not token:
        die(f"no Analytics access token: {r.text[:200]}")
    return token


def export_view(token, view_id, label):
    """Run a bulk CSV export of one Analytics view and return its text."""
    head = {"Authorization": f"Zoho-oauthtoken {token}", "ZANALYTICS-ORGID": ORG_ID}
    base = f"https://analyticsapi.zoho.com/restapi/v2/bulk/workspaces/{WORKSPACE_ID}"

    say(f"Analytics [{label}]: starting export of view {view_id}")
    r = requests.get(f"{base}/views/{view_id}/data", headers=head, timeout=(10, 60),
                     params={"CONFIG": json.dumps({"responseFormat": "csv"})})
    if r.status_code >= 400:
        die(f"Analytics [{label}] export job failed: {r.status_code} {r.text[:300]}")
    job_id = (r.json().get("data") or {}).get("jobId")

    deadline = time.time() + 900
    while time.time() < deadline:
        # The 2026-10-03 run died here on a single slow poll (ReadTimeout).
        # One hiccup while the job is still cooking is not a failure: log it
        # and poll again.
        try:
            r = requests.get(f"{base}/exportjobs/{job_id}", headers=head,
                             params={"responseFormat": "json"}, timeout=(30, 60))
            r.raise_for_status()
        except requests.RequestException as exc:
            say(f"Analytics [{label}]: poll failed ({type(exc).__name__}), retrying")
            time.sleep(10)
            continue
        info = r.json().get("data") or {}
        if info.get("jobStatus") == "JOB COMPLETED" or str(info.get("jobCode")) == "1004":
            say(f"Analytics [{label}]: export ready, downloading")
            d = requests.get(info["downloadUrl"],
                             headers={**head, "Accept-Encoding": "identity"}, timeout=(10, 900))
            d.raise_for_status()
            return strip_bom(d.text)
        if str(info.get("jobCode")) in ("1003", "1005"):
            die(f"Analytics [{label}] export failed: {info}")
        time.sleep(3)
    die(f"Analytics [{label}] export timed out after 15 minutes.")


# ------------------------------------------------------------------ compare

def compare(old, new, include_never_activated=False, label="", terminated_plans=()):
    """Devices whose plan differs between the two datasets, as dicts:

        {kind, serial, customer, crm_id, old_plan, new_plan, fields, url}

    kind is one of
        "added"       new device carrying a plan, or blank -> plan (activation)
        "terminated"  plan -> blank / "Terminated" / device gone from the table
        "changed"     any other plan -> plan (upgrade, downgrade, suspend...)

    NEVER-ACTIVATED DEVICES ARE EXCLUDED. A device counts as never activated
    when it has no plan on either side — it appears in one dataset and not the
    other, and carries no plan in the one where it exists. Those are units
    sitting in the table unprovisioned; them showing up or dropping off is not
    a billing change and just buries the real ones.
    """
    term = {t.lower() for t in terminated_plans}

    def is_term(plan):
        return not plan or plan.lower() in term

    def rec(kind, info, old_plan, new_plan):
        return {"kind": kind, "serial": info["serial"], "has_serial": info.get("has_serial", True),
                "alt_ids": info.get("alt_ids", []), "customer": info["customer"],
                "crm_id": info["crm_id"], "old_plan": old_plan or "(none)",
                "new_plan": new_plan or "(none)", "fields": info["fields"], "url": info["url"]}

    changes, skipped = [], 0
    for key, cur in new.items():
        if key in old:
            prev = old[key]
            if prev["plan"] == cur["plan"]:
                continue
            info = dict(cur)
            info["customer"] = cur["customer"] or prev["customer"]
            info["crm_id"] = cur["crm_id"] or prev["crm_id"]
            if is_term(prev["plan"]) and not is_term(cur["plan"]):
                kind = "added"                       # (none)/Terminated -> a plan
            elif is_term(cur["plan"]):
                kind = "terminated"                  # a plan -> (none)/Terminated
            else:
                kind = "changed"
            changes.append(rec(kind, info, prev["plan"], cur["plan"]))
        else:
            if is_term(cur["plan"]) and not include_never_activated:
                skipped += 1
                continue
            changes.append(rec("added", cur, "(not in old file)", cur["plan"]))

    for key in set(old) - set(new):
        prev = old[key]
        if is_term(prev["plan"]) and not include_never_activated:
            skipped += 1
            continue
        changes.append(rec("terminated", prev, prev["plan"], "(not in new data)"))

    if skipped:
        say(f"[{label}] Excluded {skipped} never-activated device(s) (no plan on either side). "
            f"Pass --include-never-activated to see them.")
    order = {"added": 0, "terminated": 1, "changed": 2}
    changes.sort(key=lambda c: (order[c["kind"]], c["customer"].lower(), c["serial"]))
    return changes



# -------------------------------------------------- CRM cancellation requests

def norm_id(v):
    """'8988228066 -605985813' -> '8988228066605985813'; 'g9 3221111410' -> 'G93221111410'."""
    return re.sub(r"[^A-Z0-9]", "", str(v or "").upper())


def serial_keys(text):
    """Every plausible identifier in a free-text serial field.

    People type one serial per line, but also '8988228066 -605985813' or
    'gaby 1V3H49YT', so each line is indexed both as a whole (all punctuation
    and spaces removed) and as its individual tokens."""
    keys = set()
    for line in re.split(r"[\r\n,;/]+", str(text or "")):
        whole = norm_id(line)
        if len(whole) >= 6:
            keys.add(whole)
        for tok in line.split():
            t = norm_id(tok)
            if len(t) >= 6:
                keys.add(t)
    return keys


def crm_token():
    if not (CRM_ID and CRM_SECRET and CRM_REFRESH):
        return ""
    r = requests.post("https://accounts.zoho.com/oauth/v2/token", data={
        "grant_type": "refresh_token", "client_id": CRM_ID,
        "client_secret": CRM_SECRET, "refresh_token": CRM_REFRESH}, timeout=60)
    if r.status_code >= 400 or not r.json().get("access_token"):
        raise RuntimeError(f"CRM token refresh failed: {r.status_code} {r.text[:200]}")
    return r.json()["access_token"]


def crm_coql_all(token, select_cols, module, where):
    """Run a COQL query and page through every row (ordered by id)."""
    rows, last_id = [], None
    while True:
        cond = where + (f" and id > {last_id}" if last_id else "")
        q = f"select {select_cols} from {module} where {cond} order by id asc limit 2000"
        r = requests.post(f"{CRM_API}/coql", headers={"Authorization": f"Zoho-oauthtoken {token}"},
                          json={"select_query": q}, timeout=(30, 120))
        if r.status_code == 204:
            return rows
        if r.status_code >= 400:
            raise RuntimeError(f"CRM COQL failed ({module}): {r.status_code} {r.text[:300]}")
        body = r.json()
        page = body.get("data") or []
        rows.extend(page)
        if not page or not (body.get("info") or {}).get("more_records"):
            return rows
        last_id = page[-1]["id"]


def load_cancellations():
    """Cancellation requests touched in the last CRM_LOOKBACK_DAYS days.

    Returns (index, requests, blobs):
        index    normalised serial/SIM -> [cancellation id, ...]
        requests cancellation id -> summary dict
        blobs    cancellation id -> normalised free text (notes + top-level
                 serial field) for a fallback substring match
    """
    token = crm_token()
    since = (datetime.datetime.now(datetime.timezone.utc)
             - datetime.timedelta(days=CRM_LOOKBACK_DAYS)).strftime("%Y-%m-%dT%H:%M:%S+00:00")
    heads = crm_coql_all(token,
        "Name, Cancellation_ID, Account_Name, Churn, Cancellation_Status, Finance_Cancellation_Status, "
        "Cancellation_Request_Date, Finance_Cancellation_Status_Timestamp, Ticket_URL, Platform_Affected, "
        "Serial_Numbers, Cancellation_Details_Notes, Additional_Notes",
        "Cancellations", f"Modified_Time >= '{since}'")
    items = crm_coql_all(token, "Parent_Id, Serial_Numbers, Vendor_Plan, Qty",
                         "Subform_2", f"Modified_Time >= '{since}'")

    requests_by_id, blobs, index = {}, {}, collections.defaultdict(list)
    for h in heads:
        cid = h["id"]
        acct = h.get("Account_Name") or {}
        requests_by_id[cid] = {
            "id": cid, "ref": h.get("Cancellation_ID") or "", "ticket": h.get("Name") or "",
            "account": acct.get("name", "") if isinstance(acct, dict) else str(acct or ""),
            "type": h.get("Churn") or "", "status": h.get("Cancellation_Status") or "",
            "finance_status": h.get("Finance_Cancellation_Status") or "",
            "requested": h.get("Cancellation_Request_Date") or "",
            "processed": (h.get("Finance_Cancellation_Status_Timestamp") or "")[:10],
            "ticket_url": h.get("Ticket_URL") or "",
            "url": CRM_CANCELLATION_URL.format(id=cid),
            "platform": ", ".join(h.get("Platform_Affected") or []),
        }
        blobs[cid] = norm_id(" ".join(str(h.get(k) or "") for k in
                                      ("Serial_Numbers", "Cancellation_Details_Notes", "Additional_Notes")))
        for key in serial_keys(h.get("Serial_Numbers")):
            index[key].append(cid)
    for it in items:
        parent = (it.get("Parent_Id") or {}).get("id")
        if not parent:
            continue
        for key in serial_keys(it.get("Serial_Numbers")):
            index[key].append(parent)
        if parent not in requests_by_id:          # subform row whose parent is older than the window
            requests_by_id[parent] = {"id": parent, "ref": "", "ticket": "", "account": "", "type": "",
                                      "status": "", "finance_status": "", "requested": "", "processed": "",
                                      "ticket_url": "", "url": CRM_CANCELLATION_URL.format(id=parent),
                                      "platform": ""}
    say(f"CRM: {len(heads)} cancellation request(s) and {len(items)} cancelled-item row(s) in the last "
        f"{CRM_LOOKBACK_DAYS} days; {len(index)} distinct serial/SIM references")
    return index, requests_by_id, blobs


def match_cancellation(change, index, requests_by_id, blobs):
    keys = [norm_id(change["serial"])] + [norm_id(a) for a in change.get("alt_ids", [])]
    keys = [k for k in keys if len(k) >= 6]
    for k in keys:
        if k in index:
            return [requests_by_id[cid] for cid in dict.fromkeys(index[k])]
    # fallback: the serial typed somewhere in the notes
    for k in keys:
        if len(k) >= 8:
            hits = [cid for cid, blob in blobs.items() if k in blob]
            if hits:
                return [requests_by_id[cid] for cid in hits]
    return []


def annotate_cancellations(results):
    """Attach c["cancellations"] (list, possibly empty) to every change and
    c["crm_checked"] = True; on any failure mark crm_checked False and move on —
    the email must still go out."""
    changes = [c for r in results for c in r["changes"]]
    if not changes:
        return
    if not CRM_REFRESH:
        say("CRM: ZOHO_CLIENT_REFRESH_TOKEN_CRM not set - cancellation requests not checked")
        for c in changes:
            c["cancellations"], c["crm_checked"] = [], False
        return
    try:
        index, reqs, blobs = load_cancellations()
    except Exception as exc:
        say(f"CRM: lookup FAILED ({exc}) - continuing without cancellation requests")
        for c in changes:
            c["cancellations"], c["crm_checked"] = [], False
        return
    found = 0
    for c in changes:
        c["cancellations"] = match_cancellation(c, index, reqs, blobs)
        c["crm_checked"] = True
        found += bool(c["cancellations"])
    terminated = [c for c in changes if c["kind"] == "terminated"]
    say(f"CRM: {sum(1 for c in terminated if c['cancellations'])} of {len(terminated)} terminated device(s) "
        f"have a cancellation request; {found - sum(1 for c in terminated if c['cancellations'])} other "
        f"change(s) also reference one")


def cancel_text(c):
    """Short plain-text summary of a change's cancellation match."""
    if not c.get("crm_checked"):
        return "not checked"
    if not c.get("cancellations"):
        return "NO REQUEST FOUND"
    return "; ".join(f"{q['ref'] or q['id']} {q['ticket']} - {q['status']}"
                     f"{' / ' + q['finance_status'] if q['finance_status'] else ''}"
                     f"{' (req ' + q['requested'] + ')' if q['requested'] else ''}"
                     for q in c["cancellations"])


# -------------------------------------------------------------------- email

def _row_values(c):
    q = (c.get("cancellations") or [None])[0]
    return ([KIND_LABEL[c["kind"]], c["customer"], crm_link(c), c["serial"], device_link(c),
             c["old_plan"], c["new_plan"]] + list(c["fields"].values())
            + [cancel_text(c), q["url"] if q else "", q["ticket_url"] if q else ""])


def _row_headers(source):
    return (["Change", "Customer", "CRM Link", "Serial", "Device Link", "Old Plan", "New Plan"]
            + [lab for lab, _, _ in source.get("columns", [])]
            + ["Cancellation Request", "Cancellation Link", "Ticket Link"])


def build_csv(source, changes):
    buf = io.StringIO(newline="")
    w = csv.writer(buf, lineterminator="\n")
    w.writerow(_row_headers(source))
    for c in changes:
        w.writerow(_row_values(c))
    return buf.getvalue()


def build_xlsx(results):
    """report.xlsx with one sheet per source (Geotab, Zenduit). Returns bytes,
    or None if openpyxl is not installed (the CSVs are attached instead)."""
    try:
        from openpyxl import Workbook
        from openpyxl.styles import Alignment, Font, PatternFill
        from openpyxl.utils import get_column_letter
    except ImportError:
        say("openpyxl not installed - attaching CSVs instead of report.xlsx")
        return None
    wb = Workbook()
    wb.remove(wb.active)
    for r in results:
        ws = wb.create_sheet(r["label"][:31])
        headers = _row_headers(r["source"])
        ws.append(headers)
        for cell in ws[1]:
            cell.font = Font(bold=True, color="FFFFFF")
            cell.fill = PatternFill("solid", fgColor=BRAND)
            cell.alignment = Alignment(vertical="center")
        for c in r["changes"]:
            ws.append(_row_values(c))
            row = ws.max_row
            for col_idx, header in enumerate(headers, start=1):
                v = ws.cell(row=row, column=col_idx).value
                if header in ("CRM Link", "Device Link", "Cancellation Link", "Ticket Link") and v:
                    ws.cell(row=row, column=col_idx).hyperlink = v
                    ws.cell(row=row, column=col_idx).font = Font(color="0563C1", underline="single")
        ws.freeze_panes = "A2"
        ws.auto_filter.ref = ws.dimensions
        for col_idx, header in enumerate(headers, start=1):
            width = max([len(str(header))] + [len(str(ws.cell(row=i, column=col_idx).value or ""))
                                               for i in range(2, min(ws.max_row, 300) + 1)])
            ws.column_dimensions[get_column_letter(col_idx)].width = min(max(10, width + 2), 60)
        if not r["changes"]:
            ws.append(["No changes" if not r["first_run"] else "Baseline created - nothing to compare yet"])
    buf = io.BytesIO()
    wb.save(buf)
    return buf.getvalue()


_google = None


def google_client():
    """One shared Google OAuth client (Drive + Gmail use the same refresh token)."""
    global _google
    if _google is None:
        _google = DriveClient(GDRIVE_CLIENT_ID, GDRIVE_CLIENT_SECRET, GDRIVE_REFRESH_TOKEN, log=say)
    return _google


def build_message(subject, html, text, attachments=(), to=None):
    msg = MIMEMultipart("mixed")
    msg["Subject"] = subject
    msg["From"] = MAIL_FROM
    msg["To"] = ", ".join(to or MAIL_TO)
    body = MIMEMultipart("alternative")
    body.attach(MIMEText(text, "plain"))
    body.attach(MIMEText(html, "html"))
    msg.attach(body)
    for name, content in attachments:
        data = content if isinstance(content, (bytes, bytearray)) else content.encode("utf-8")
        part = MIMEApplication(data, Name=name)
        part["Content-Disposition"] = f'attachment; filename="{name}"'
        msg.attach(part)
    return msg


def send_via_gmail_api(msg):
    """Send through the Gmail REST API with the Google refresh token (needs the
    gmail.send permission, which `python main.py get-token` requests). HTTPS
    only - no SMTP, no app password. Gmail drops SMTP logins coming from GitHub's
    shared cloud addresses, which is exactly what killed the first run."""
    raw = base64.urlsafe_b64encode(msg.as_bytes()).decode("ascii")
    r = requests.post("https://gmail.googleapis.com/gmail/v1/users/me/messages/send",
                      headers={"Authorization": f"Bearer {google_client().token()}"},
                      json={"raw": raw}, timeout=(30, 300))
    if r.status_code >= 400:
        hint = ""
        if r.status_code == 403:
            hint = ("\n   -> 403 usually means the token lacks the gmail.send permission "
                    "(re-run `python main.py get-token`) or the Gmail API is not enabled "
                    "in the Google Cloud project.")
        raise RuntimeError(f"Gmail API send failed: {r.status_code} {r.text[:400]}{hint}")


def send_via_smtp(msg, to=None):
    if not (SMTP_USER and SMTP_PASS):
        die("SMTP_USERNAME / SMTP_PASSWORD not set (or set MAIL_VIA=gmail_api with a Google token)")
    with smtplib.SMTP(SMTP_HOST, SMTP_PORT, timeout=60) as s:
        s.starttls()
        s.login(SMTP_USER, SMTP_PASS)
        s.sendmail(MAIL_FROM, to or MAIL_TO, msg.as_string())


def send_mail(subject, html, text, attachments=(), to=None):
    """attachments: iterable of (filename, text or bytes). to: recipients (default MAIL_TO).

    MAIL_VIA=gmail_api (default whenever a Google refresh token is configured)
    sends through the Gmail API; MAIL_VIA=smtp uses SMTP with the app password.
    If the API send fails and SMTP credentials exist, SMTP is tried as a fallback."""
    to = to or MAIL_TO
    if not (MAIL_FROM and to):
        die("EMAIL_FROM / EMAIL_TO not set")
    msg = build_message(subject, html, text, attachments, to)
    if MAIL_VIA == "gmail_api":
        try:
            send_via_gmail_api(msg)
            say(f"Emailed {', '.join(to)} (Gmail API)")
            return
        except Exception as exc:
            if not SMTP_PASS:
                raise
            say(f"Gmail API send failed ({exc}); falling back to SMTP")
    send_via_smtp(msg, to)
    say(f"Emailed {', '.join(to)} (SMTP)")


KIND_LABEL = {"added": "Added", "terminated": "Terminated", "changed": "Plan Change"}
BRAND = env("EMAIL_BRAND_COLOR", "1F3A5F")       # header band + table header (hex, no #)


def esc(v):
    return html_mod.escape(str(v if v is not None else ""), quote=True)


def crm_link(c):
    cid = (c.get("crm_id") or "").strip()
    return CRM_ACCOUNT_URL.format(crm_id=cid) if cid.isdigit() and CRM_ACCOUNT_URL else ""


def device_link(c):
    tpl = c.get("_device_url") or ""
    if not tpl:
        return ""
    try:
        url = tpl.format(**{k: urllib.parse.quote(str(v or ""), safe="") for k, v in c["url"].items()})
    except (KeyError, IndexError):
        return ""
    return "" if "{" in url else url


def a(text, url):
    text = esc(text) if text else "-"
    return f'<a href="{esc(url)}" style="color:#1a5fb4;text-decoration:none">{text}</a>' if url else text


def counts(changes):
    return {"added": sum(1 for c in changes if c["kind"] == "added"),
            "terminated": sum(1 for c in changes if c["kind"] == "terminated"),
            "changed": sum(1 for c in changes if c["kind"] == "changed"),
            "customers": len({c["customer"].lower() for c in changes if c["customer"]}),
            "no_request": sum(1 for c in changes if c["kind"] == "terminated"
                              and c.get("crm_checked") and not c.get("cancellations"))}


ROW_CAP = int(env("EMAIL_ROW_CAP", "300"))      # rows per table in the email body; the rest is in report.xlsx
CARD_COLORS = {"added": "#1a7f4b", "terminated": "#b3261e", "changed": "#1a5fb4"}
CARD_LABELS = {"added": "Devices Added", "terminated": "Terminated", "changed": "Plan Changes"}


def card_html(number, caption, color, note=""):
    return (f"<td style='padding:0 6px;width:33%'><table role='presentation' cellpadding='0' cellspacing='0' "
            f"style='width:100%;background:#f4f6fa;border-radius:8px;border-bottom:3px solid {color}'>"
            f"<tr><td style='padding:16px 10px;text-align:center'>"
            f"<div style='font-size:30px;font-weight:700;color:{color};line-height:1'>{number}</div>"
            f"<div style='font-size:11px;color:#5b6472;text-transform:uppercase;letter-spacing:.04em;margin-top:6px'>{caption}</div>"
            f"{f'<div style=font-size:11px;color:#b3261e;margin-top:4px>{note}</div>' if note else ''}"
            f"</td></tr></table></td>")


def cards_row(changes):
    n = counts(changes)
    note = f"{n['no_request']} without a cancellation request" if n["no_request"] else ""
    return ("<table role='presentation' cellpadding='0' cellspacing='0' style='width:100%;margin:12px 0 4px'><tr>"
            + card_html(n["added"], CARD_LABELS["added"], CARD_COLORS["added"])
            + card_html(n["terminated"], CARD_LABELS["terminated"], CARD_COLORS["terminated"], note)
            + card_html(n["changed"], CARD_LABELS["changed"], CARD_COLORS["changed"])
            + "</tr></table>")


def change_table_html(source, changes):
    """ONE table per source: every changed device, with a Change column."""
    th = (f"padding:7px 9px;background:#{BRAND};color:#fff;font-size:12px;text-align:left;"
          "white-space:nowrap;border-right:1px solid rgba(255,255,255,.15)")
    td = "padding:6px 9px;border-bottom:1px solid #e3e6eb;font-size:12px;vertical-align:top"
    extra = [lab for lab, _, _ in source.get("columns", [])]
    crm_checked = any(c.get("crm_checked") for c in changes)
    headers = ["Change", "Customer", "Serial", "Plan (old &rarr; new)"] + extra + ["Cancellation Request"]
    head = "".join(f"<th style='{th}'>{h}</th>" for h in headers)
    rows = []
    for i, c in enumerate(changes[:ROW_CAP]):
        bg = "#ffffff" if i % 2 == 0 else "#f8f9fb"
        color = CARD_COLORS[c["kind"]]
        kind = f"<span style='color:{color};font-weight:600;white-space:nowrap'>{KIND_LABEL[c['kind']]}</span>"
        if c["kind"] == "added":
            plan = f"<span style='color:#8a94a3'>{esc(c['old_plan'])}</span> &rarr; <b>{esc(c['new_plan'])}</b>"
        elif c["kind"] == "terminated":
            plan = f"{esc(c['old_plan'])} &rarr; <span style='color:#b3261e;font-weight:600'>{esc(c['new_plan'])}</span>"
        else:
            plan = f"{esc(c['old_plan'])} &rarr; <b>{esc(c['new_plan'])}</b>"
        if c["kind"] != "terminated":
            canc = "<span style='color:#8a94a3'>-</span>"
        elif not c.get("crm_checked"):
            canc = "<span style='color:#8a94a3'>not checked</span>"
        elif not c.get("cancellations"):
            canc = "<span style='color:#b3261e;font-weight:600'>No request found</span>"
        else:
            canc = "<br>".join(
                a(q["ref"] or "request", q["url"])
                + (f" &middot; {a(q['ticket'], q['ticket_url'])}" if q["ticket"] else "")
                + f" &middot; {esc(q['status'])}"
                + (f" / {esc(q['finance_status'])}" if q["finance_status"] else "")
                + (f" <span style='color:#8a94a3'>(req {esc(q['requested'])})</span>" if q["requested"] else "")
                for q in c["cancellations"])
        cells = [kind, a(c["customer"], crm_link(c)),
                 f"<span style='font-family:Consolas,Menlo,monospace;white-space:nowrap'>"
                 f"{a(c['serial'] if c.get('has_serial', True) else '-', device_link(c))}</span>",
                 plan] + [esc(v) or "-" for v in c["fields"].values()] + [canc]
        rows.append(f"<tr style='background:{bg}'>" + "".join(f"<td style='{td}'>{x}</td>" for x in cells) + "</tr>")
    more = (f"<p style='font-size:12px;color:#5b6472;margin:6px 0 0'>&hellip; and {len(changes) - ROW_CAP} more "
            f"in the attached report.xlsx.</p>" if len(changes) > ROW_CAP else "")
    return (f"<div style='overflow-x:auto;margin-top:10px'><table cellpadding='0' cellspacing='0' "
            f"style='border-collapse:collapse;width:100%;min-width:900px'>"
            f"<tr>{head}</tr>{''.join(rows)}</table></div>{more}")


def source_html(result):
    label = result["label"]
    head = (f"<h2 style='font-size:17px;margin:26px 0 2px;padding-top:16px;border-top:2px solid #e3e6eb;"
            f"color:#1f2a37'>{esc(label)}</h2>")
    if result["first_run"]:
        return head + (f"<p style='font-size:13px;color:#5b6472'>No baseline existed for {esc(label)}; created "
                       f"<b>{esc(result['baseline_name'])}</b> with {result['count']:,} devices. Changes will be "
                       f"reported from the next run.</p>")
    if not result["changes"]:
        return head + "<p style='font-size:13px;color:#5b6472'>No device plan changes.</p>"
    n = counts(result["changes"])
    return head + (f"<div style='font-size:12px;color:#5b6472'>{n['customers']} customer(s) affected</div>"
                   + cards_row(result["changes"])
                   + change_table_html(result["source"], result["changes"]))


def digest_html(results, when):
    all_changes = [c for r in results for c in r["changes"]]
    labels = " &amp; ".join(esc(r["label"]) for r in results)
    checked = any(c.get("crm_checked") for c in all_changes)
    intro = (f"Device activations, terminations and plan changes since the previous run, for {labels}. "
             f"Customer names open the Zoho CRM account; serial numbers open the device page where a link is "
             f"configured. The full breakdown is attached as <b>report.xlsx</b> (one sheet per source).")
    crm_line = ("Terminated devices were checked against Zoho CRM cancellation requests: the last column shows "
                "the matching request (reference &middot; ticket &middot; status), or <b style='color:#b3261e'>"
                "No request found</b>."
                if checked else
                "Cancellation requests were <b>not</b> checked this run (CRM token not configured or lookup failed).")
    overall = ""
    if len(results) > 1:
        overall = ("<h2 style='font-size:16px;margin:22px 0 2px;color:#1f2a37'>All sources</h2>"
                   + cards_row(all_changes))
    return (f"<html><body style='margin:0;padding:0;background:#eef1f5'>"
            f"<table role='presentation' cellpadding='0' cellspacing='0' style='width:100%;background:#eef1f5'><tr><td align='center' style='padding:18px 8px'>"
            f"<table role='presentation' cellpadding='0' cellspacing='0' style='width:100%;max-width:1200px;background:#fff;border-radius:10px;overflow:hidden;font-family:Segoe UI,Helvetica,Arial,sans-serif;color:#1f2a37'>"
            f"<tr><td style='background:#{BRAND};padding:18px 24px'>"
            f"<div style='font-size:11px;letter-spacing:.12em;color:#c9d4e3;text-transform:uppercase'>Device Billing Update</div>"
            f"<div style='font-size:20px;font-weight:700;color:#fff;margin-top:4px'>{labels} &middot; Daily</div>"
            f"<div style='font-size:12px;color:#c9d4e3;margin-top:4px'>{esc(when)}</div></td></tr>"
            f"<tr><td style='padding:18px 24px 26px'>"
            f"<p style='font-size:13px;line-height:1.5;margin:0'>{intro}</p>"
            f"<p style='font-size:12px;line-height:1.5;margin:8px 0 0;color:#5b6472'>{crm_line}</p>"
            f"{overall}"
            f"{''.join(source_html(r) for r in results)}"
            f"</td></tr></table></td></tr></table></body></html>")


def digest_text(results, when):
    lines = [f"Device billing update - {' & '.join(r['label'] for r in results)} - {when}", ""]
    for r in results:
        lines.append(f"== {r['label']} ==")
        if r["first_run"]:
            lines.append(f"Baseline created with {r['count']} devices; nothing to compare yet.")
            lines.append("")
            continue
        n = counts(r["changes"])
        lines.append(f"Devices added: {n['added']}   Terminated: {n['terminated']} "
                     f"({n['no_request']} without a cancellation request)   Plan changes: {n['changed']}")
        for c in r["changes"]:
            extra = f"  [{cancel_text(c)}]" if c["kind"] == "terminated" else ""
            lines.append(f"  {KIND_LABEL[c['kind']]:<11} {c['serial']}  ({c['customer'] or '-'})  "
                         f"{c['old_plan']} -> {c['new_plan']}{extra}")
        lines.append("")
    lines.append("Full breakdown attached as report.xlsx.")
    return "\n".join(lines)


def email_results(results):
    """One email, a section per source in SOURCES order (Geotab, then Zenduit)."""
    when = time.strftime("%b %d, %Y %H:%M UTC", time.gmtime())
    created = [r["label"] for r in results if r["first_run"]]
    subject = (f"Device billing changes - {' & '.join(r['label'] for r in results)} - "
               f"{time.strftime('%d %b %Y', time.gmtime())}")
    if created:
        subject += f" - baseline created: {', '.join(created)}"
    xlsx = build_xlsx(results)
    if xlsx:
        attachments = [("report.xlsx", xlsx)]
    else:
        attachments = [(f"plan_changes_{r['key']}.csv", build_csv(r["source"], r["changes"]))
                       for r in results if r["changes"]]
    for r in results:
        if not r["first_run"]:
            n = counts(r["changes"])
            say(f"Email summary [{r['label']}]: {n['added']} added, {n['terminated']} terminated "
                f"({n['no_request']} without request), {n['changed']} plan changes")
    send_mail(subject, digest_html(results, when), digest_text(results, when), attachments)


def email_failure(err):
    """A scheduled job that dies quietly is worse than one that never ran."""
    try:
        text = ("The device plan-change check failed.\n\n"
                f"{err}\n\nLog: {LOG_PATH}\n")
        html = (f"<html><body style='font-family:sans-serif;font-size:14px'>"
                f"<p><b>The device plan-change check failed.</b></p>"
                f"<pre style='background:#f6f6f6;padding:10px;font-size:12px'>{err}</pre>"
                f"<p style='color:#777;font-size:11px'>Log: {LOG_PATH}</p></body></html>")
        send_mail("Device plan check FAILED", html, text, to=FAILURE_TO)
    except Exception:
        say("Could not send the failure email either.")


# ---------------------------------------------------------- baseline update

def prune(directory, prefix, keep):
    """Keep the newest `keep` files starting with `prefix`; delete the rest."""
    try:
        files = sorted(f for f in os.listdir(directory) if f.startswith(prefix))
    except OSError:
        return
    for name in files[:-keep] if keep > 0 else files:
        try:
            os.remove(os.path.join(directory, name))
        except OSError as exc:
            say(f"Could not delete old file {name}: {exc}")
    if len(files) > keep:
        say(f"Pruned {len(files) - keep} old '{prefix}*' file(s), kept the newest {keep}.")


def write_atomic(path, text):
    """Write to a temp name, then move into place, so an interrupted run cannot
    leave a half-written file — and Google Drive cannot sync a truncated one.
    A path ending in .gz is written gzipped (git stores a 10x smaller file,
    and read_local_csv reads either form)."""
    tmp = path + ".tmp"
    if path.lower().endswith(".gz"):
        with gzip.open(tmp, "wt", encoding="utf-8", newline="", compresslevel=6) as fh:
            fh.write(text)
    else:
        with open(tmp, "w", encoding="utf-8", newline="") as fh:
            fh.write(text)
    os.replace(tmp, path)          # atomic on Windows and POSIX


def baseline_stem(source):
    """'Geotab_Devices.csv.gz' / 'Geotab_Devices.csv' -> 'Geotab_Devices'."""
    name = source["baseline"]
    for ext in (".csv.gz", ".gz", ".csv"):
        if name.lower().endswith(ext):
            return name[:-len(ext)]
    return os.path.splitext(name)[0]


def update_baseline_file(source, baseline_path, new_text):
    """Back up the current baseline, then replace it with the new data.

    The backup is taken BEFORE anything is overwritten, every single time
    (unless KEEP_BACKUPS=0, i.e. the folder is a git repo whose history already
    keeps every version). A previous baseline was lost to a run that refreshed
    it in place, which made the change it should have caught unrecoverable. A
    gzipped copy costs almost nothing against that.
    """
    stem = baseline_stem(source)                            # e.g. Geotab_Devices
    if KEEP_BACKUPS > 0:
        stamp = time.strftime("%Y%m%d_%H%M%S")
        backup_dir = os.path.join(DISCREPANCY_DIR, BACKUP_SUBDIR)
        os.makedirs(backup_dir, exist_ok=True)
        backup = os.path.join(backup_dir, f"{stem}_{stamp}.csv.gz")
        with open(baseline_path, "rb") as src:
            raw = src.read()
        if raw[:2] == b"\x1f\x8b":                            # already gzipped: copy as-is
            with open(backup, "wb") as dst:
                dst.write(raw)
        else:
            with gzip.open(backup, "wb", compresslevel=6) as dst:
                dst.write(raw)
        say(f"[{source['label']}] Backed up previous baseline -> {backup} "
            f"({os.path.getsize(backup) / 1024 / 1024:.1f} MB gzipped)")
        prune(backup_dir, f"{stem}_", KEEP_BACKUPS)
    else:
        say(f"[{source['label']}] KEEP_BACKUPS=0: no backup copy kept")

    write_atomic(baseline_path, new_text)
    say(f"[{source['label']}] Baseline updated: {baseline_path}")

    prune(DISCREPANCY_DIR, f"plan_changes_{source['key']}_", KEEP_REPORTS)


# --------------------------------------------------------------------- main

def process_source(source, token, include_never):
    """Steps 1-3 for one source. Returns a result dict; nothing is written to
    the baseline here."""
    label = source["label"]
    baseline_path = os.path.join(DISCREPANCY_DIR, source["baseline"])
    say(f"--- {label}: baseline {baseline_path}")

    new_text = export_view(token, source["view_id"], label)
    new = to_plan_map(new_text, source, f"NEW {label} (Analytics)")

    result = {"key": source["key"], "label": label, "source": source,
              "baseline_path": baseline_path, "baseline_name": source["baseline"],
              "new_text": new_text, "count": len(new),
              "first_run": False, "changes": [], "report_path": ""}

    if not os.path.exists(baseline_path):
        # First run for this source. Nothing to compare against; the baseline is
        # laid down in the update step and the email says so plainly rather
        # than reporting "no changes".
        say(f"[{label}] No baseline found - will create {baseline_path} with {len(new)} devices.")
        result["first_run"] = True
        return result

    old = to_plan_map(read_local_csv(baseline_path), source, f"OLD {label} ({source['baseline']})")
    changes = compare(old, new, include_never_activated=include_never, label=label,
                      terminated_plans=source.get("terminated_plans", ()))
    for c in changes:
        c["_device_url"] = source.get("device_url", "")
    kinds = collections.Counter(c["kind"] for c in changes)
    say(f"[{label}] {len(changes)} change(s): {kinds.get('added', 0)} added, "
        f"{kinds.get('terminated', 0)} terminated, {kinds.get('changed', 0)} plan changes")
    for c in changes[:50]:
        say(f"    {KIND_LABEL[c['kind']]:<11} {c['serial']}  ({c['customer'] or '-'})  {c['old_plan']} -> {c['new_plan']}")
    if len(changes) > 50:
        say(f"    ... and {len(changes) - 50} more")

    if changes:
        report_path = os.path.join(
            DISCREPANCY_DIR, f"plan_changes_{source['key']}_{time.strftime('%Y%m%d_%H%M')}.csv")
        with open(report_path, "w", encoding="utf-8", newline="") as fh:
            fh.write(build_csv(source, changes))
        say(f"[{label}] Wrote {report_path}")
        result["report_path"] = report_path
    result["changes"] = changes
    return result


def run():
    skip_update = "--no-update-baseline" in sys.argv
    include_never = "--include-never-activated" in sys.argv

    sources = SOURCES
    if "--only" in sys.argv:
        want = sys.argv[sys.argv.index("--only") + 1].lower()
        sources = [s for s in SOURCES if s["key"] == want]
        if not sources:
            die(f"--only {want}: unknown source. Choose from "
                + ", ".join(s["key"] for s in SOURCES))

    say("=" * 60)
    say(f"Folder:  {DISCREPANCY_DIR}")
    say(f"Sources: {', '.join(s['label'] for s in sources)}")

    if not os.path.isdir(DISCREPANCY_DIR):
        die(f"the folder {DISCREPANCY_DIR} does not exist or is not reachable.\n"
            "A mapped drive like G: only exists while Google Drive is running and you are "
            "logged in. Tick 'Run only when user is logged on' in Task Scheduler, or point "
            "DISCREPANCY_DIR at a real local path.")

    token = analytics_token()
    results = [process_source(s, token, include_never) for s in sources]
    annotate_cancellations(results)

    # ---- one email for everything, Geotab section first, Zenduit second ----
    # If this raises, the script exits and no baseline below is touched — which
    # is the point. Rolling a baseline forward after a failed send would erase
    # the very changes nobody has been told about.
    if any(r["changes"] or r["first_run"] for r in results):
        email_results(results)
    else:
        say("No changes in any source - no email sent.")

    # ---- baseline update, last thing, only after the email is safely away ----
    for r in results:
        if r["first_run"]:
            # Always lay down a missing baseline, even with --no-update-baseline:
            # without it the next run would have nothing to compare against.
            write_atomic(r["baseline_path"], r["new_text"])
            say(f"[{r['label']}] Created baseline {r['baseline_path']} with {r['count']} devices.")
        elif skip_update:
            say(f"[{r['label']}] --no-update-baseline: {r['baseline_path']} left unchanged. "
                "The next run will report this same list again.")
        else:
            update_baseline_file(r["source"], r["baseline_path"], r["new_text"])


# =============================================================================
#  Google Drive storage (used when STORAGE=gdrive)
# =============================================================================

API = "https://www.googleapis.com/drive/v3"
UPLOAD = "https://www.googleapis.com/upload/drive/v3"
FOLDER_MIME = "application/vnd.google-apps.folder"
# supportsAllDrives makes the same code work if the folder is ever moved into
# a Shared Drive.
COMMON = {"supportsAllDrives": "true"}


class DriveError(RuntimeError):
    pass


# ----------------------------------------------------------------- low level

class DriveClient:
    """Thin wrapper over the Drive v3 REST API with a self-refreshing token."""

    def __init__(self, client_id, client_secret, refresh_token, log=print):
        if not (client_id and client_secret and refresh_token):
            raise DriveError("GDRIVE_CLIENT_ID / GDRIVE_CLIENT_SECRET / GDRIVE_REFRESH_TOKEN not set")
        self.client_id = client_id
        self.client_secret = client_secret
        self.refresh_token = refresh_token
        self.log = log
        self._token = None
        self._token_expiry = 0

    # -- auth --
    def token(self):
        if self._token and time.time() < self._token_expiry - 120:
            return self._token
        r = requests.post("https://oauth2.googleapis.com/token", data={
            "grant_type": "refresh_token", "client_id": self.client_id,
            "client_secret": self.client_secret, "refresh_token": self.refresh_token},
            timeout=60)
        if r.status_code >= 400:
            raise DriveError(f"Google token refresh failed: {r.status_code} {r.text[:300]}\n"
                             "If this says invalid_grant the refresh token was revoked or "
                             "expired (an 'External / Testing' OAuth app expires tokens after "
                             "7 days — the consent screen must be 'Internal'). Re-run "
                             "`python main.py get-token` and update the GDRIVE_REFRESH_TOKEN secret.")
        body = r.json()
        self._token = body["access_token"]
        self._token_expiry = time.time() + int(body.get("expires_in", 3600))
        return self._token

    def _headers(self, extra=None):
        h = {"Authorization": f"Bearer {self.token()}"}
        if extra:
            h.update(extra)
        return h

    def _check(self, r, what):
        if r.status_code >= 400:
            raise DriveError(f"Drive {what} failed: {r.status_code} {r.text[:400]}")
        return r

    # -- read --
    def list_folder(self, folder_id):
        """Every non-trashed item directly inside folder_id: [{id,name,mimeType,size,modifiedTime}]."""
        files, page_token = [], None
        while True:
            params = {**COMMON, "includeItemsFromAllDrives": "true", "pageSize": 1000,
                      "q": f"'{folder_id}' in parents and trashed = false",
                      "fields": "nextPageToken,files(id,name,mimeType,size,modifiedTime)"}
            if page_token:
                params["pageToken"] = page_token
            r = self._check(requests.get(f"{API}/files", headers=self._headers(),
                                         params=params, timeout=(10, 120)), "list")
            body = r.json()
            files.extend(body.get("files", []))
            page_token = body.get("nextPageToken")
            if not page_token:
                return files

    def download(self, file_id, local_path):
        with requests.get(f"{API}/files/{file_id}", headers=self._headers(),
                          params={**COMMON, "alt": "media"}, stream=True,
                          timeout=(10, 900)) as r:
            self._check(r, "download")
            tmp = local_path + ".part"
            with open(tmp, "wb") as fh:
                for chunk in r.iter_content(1024 * 1024):
                    fh.write(chunk)
            os.replace(tmp, local_path)

    # -- write --
    def _resumable(self, method, url, metadata, local_path):
        """Resumable upload in one shot. (Multipart uploads are capped at 5 MB,
        which a device export can exceed; resumable has no such cap.)"""
        size = os.path.getsize(local_path)
        r = self._check(requests.request(
            method, url, headers=self._headers({
                "Content-Type": "application/json; charset=UTF-8",
                "X-Upload-Content-Type": "application/octet-stream",
                "X-Upload-Content-Length": str(size)}),
            params={**COMMON, "uploadType": "resumable",
                    "fields": "id,name,size,modifiedTime"},
            data=json.dumps(metadata), timeout=(10, 120)), "upload start")
        session_url = r.headers.get("Location")
        if not session_url:
            raise DriveError("Drive upload start returned no session URL")
        with open(local_path, "rb") as fh:
            r = requests.put(session_url, headers={"Content-Type": "application/octet-stream",
                                                   "Content-Length": str(size)},
                             data=fh, timeout=(10, 1800))
        return self._check(r, "upload").json()

    def create_file(self, folder_id, name, local_path):
        return self._resumable("POST", f"{UPLOAD}/files",
                               {"name": name, "parents": [folder_id]}, local_path)

    def update_file(self, file_id, local_path):
        """Replace the content of an existing file. Keeps id, owner, sharing and
        the file's own revision history in Drive."""
        return self._resumable("PATCH", f"{UPLOAD}/files/{file_id}", {}, local_path)

    def delete(self, file_id):
        self._check(requests.delete(f"{API}/files/{file_id}", headers=self._headers(),
                                    params=COMMON, timeout=(10, 60)), "delete")

    def create_folder(self, parent_id, name):
        r = self._check(requests.post(f"{API}/files", headers=self._headers(
            {"Content-Type": "application/json; charset=UTF-8"}),
            params={**COMMON, "fields": "id,name"},
            data=json.dumps({"name": name, "mimeType": FOLDER_MIME, "parents": [parent_id]}),
            timeout=(10, 60)), "create folder")
        return r.json()


# ---------------------------------------------------------------- high level

def _snapshot(directory):
    """name -> (size, mtime) for the regular files directly in `directory`."""
    out = {}
    try:
        for name in os.listdir(directory):
            p = os.path.join(directory, name)
            if os.path.isfile(p):
                st = os.stat(p)
                out[name] = (st.st_size, st.st_mtime)
    except FileNotFoundError:
        pass
    return out


def _by_name(items, log):
    """name -> item, keeping the newest when Drive holds duplicates (Drive
    allows two files with the same name in one folder; the sync does not)."""
    out = {}
    for it in sorted(items, key=lambda i: i.get("modifiedTime", "")):
        if it["name"] in out:
            log(f"Drive: duplicate name '{it['name']}' in folder - using the newest copy")
        out[it["name"]] = it
    return out


class DriveSync:
    def __init__(self, client, folder_id, work_dir, log=print,
                 backup_subdir="baseline_backups"):
        if not folder_id:
            raise DriveError("GDRIVE_FOLDER_ID not set")
        self.c = client
        self.folder_id = folder_id
        self.work_dir = work_dir
        self.log = log
        self.backup_subdir = backup_subdir
        self._before = {}

    def pull(self, names):
        """Download the named files (baselines, log) into work_dir. A name that
        does not exist on Drive is simply skipped — that is the first run."""
        os.makedirs(self.work_dir, exist_ok=True)
        remote = _by_name([i for i in self.c.list_folder(self.folder_id)
                           if i.get("mimeType") != FOLDER_MIME], self.log)
        for name in names:
            it = remote.get(name)
            if not it:
                self.log(f"Drive: '{name}' not in folder (will be created on push)")
                continue
            self.c.download(it["id"], os.path.join(self.work_dir, name))
            self.log(f"Drive: downloaded {name} ({int(it.get('size') or 0) / 1024 / 1024:.1f} MB, "
                     f"last modified in Drive {it.get('modifiedTime', '?')[:16].replace('T', ' ')} UTC)")
        self._before = _snapshot(self.work_dir)

    def push(self, keep_backups=0, keep_report_prefixes=(), keep_reports=0, only=None):
        """Upload every file in work_dir that is new or changed since pull(),
        mirror new backups into the backups subfolder, then prune on Drive.

        only: an iterable of file names. When given, ONLY those names are ever
        uploaded and nothing else is created, mirrored or pruned on Drive —
        used to keep the Drive folder down to just the baseline tables."""
        after = _snapshot(self.work_dir)
        changed = [n for n, sig in after.items()
                   if not n.endswith((".tmp", ".part")) and self._before.get(n) != sig]
        if only is not None:
            only = set(only)
            changed = [n for n in changed if n in only]
        if not changed:
            self.log("Drive: nothing changed, nothing to upload")
        items = self.c.list_folder(self.folder_id)
        remote = _by_name([i for i in items if i.get("mimeType") != FOLDER_MIME], self.log)
        for name in sorted(changed):
            path = os.path.join(self.work_dir, name)
            if name in remote:
                info = self.c.update_file(remote[name]["id"], path)
                self.log(f"Drive: updated  {name} (now {os.path.getsize(path) / 1024 / 1024:.1f} MB, "
                         f"Drive modifiedTime {str(info.get('modifiedTime', '?'))[:16].replace('T', ' ')} UTC)")
            else:
                self.c.create_file(self.folder_id, name, path)
                self.log(f"Drive: uploaded {name}")

        if only is not None:
            return                      # baselines only: no backups, reports or pruning on Drive

        # backups: anything in work_dir/baseline_backups is new this run
        local_backups = os.path.join(self.work_dir, self.backup_subdir)
        new_backups = sorted(_snapshot(local_backups))
        folders = {i["name"]: i for i in items if i.get("mimeType") == FOLDER_MIME}
        backup_folder = folders.get(self.backup_subdir)
        if new_backups:
            if not backup_folder:
                backup_folder = self.c.create_folder(self.folder_id, self.backup_subdir)
                self.log(f"Drive: created folder {self.backup_subdir}/")
            for name in new_backups:
                self.c.create_file(backup_folder["id"], name, os.path.join(local_backups, name))
                self.log(f"Drive: uploaded {self.backup_subdir}/{name}")

        # prune on Drive, mirroring prune() above
        for prefix in keep_report_prefixes:
            self._prune(self.folder_id, prefix, keep_reports)
        if backup_folder and keep_backups > 0:
            for prefix in self._backup_prefixes(new_backups):
                self._prune(backup_folder["id"], prefix, keep_backups)

    @staticmethod
    def _backup_prefixes(names):
        """'Geotab_Devices_20261006_043000.csv.gz' -> 'Geotab_Devices_'."""
        out = set()
        for n in names:
            stem = n.rsplit("_", 2)[0] if n.count("_") >= 2 else n
            out.add(stem + "_")
        return sorted(out)

    def _prune(self, folder_id, prefix, keep):
        if keep <= 0:
            return
        items = sorted((i for i in self.c.list_folder(folder_id)
                        if i.get("mimeType") != FOLDER_MIME and i["name"].startswith(prefix)),
                       key=lambda i: i["name"])          # names carry the timestamp
        for it in items[:-keep]:
            try:
                self.c.delete(it["id"])
            except DriveError as exc:
                self.log(f"Drive: could not delete {it['name']}: {exc}")
        if len(items) > keep:
            self.log(f"Drive: pruned {len(items) - keep} old '{prefix}*' file(s), kept the newest {keep}")


# --------------------------------------------------------------------- main

def make_drive_sync():
    """Only used when STORAGE=gdrive."""
    client = DriveClient(GDRIVE_CLIENT_ID, GDRIVE_CLIENT_SECRET, GDRIVE_REFRESH_TOKEN, log=say)
    return DriveSync(client, GDRIVE_FOLDER_ID, DISCREPANCY_DIR, log=say,
                     backup_subdir=BACKUP_SUBDIR)


def main():
    sync = None
    exit_code = 0
    try:
        if STORAGE == "gdrive":
            sync = make_drive_sync()
            say("=" * 60)
            say(f"Drive: pulling baselines and log from folder {GDRIVE_FOLDER_ID}")
            baselines = [s["baseline"] for s in SOURCES]
            sync.pull(baselines + ([LOG_NAME] if GDRIVE_SYNC_EXTRAS else []))
        run()
    except SystemExit as exc:            # die() — already logged
        exit_code = exc.code if isinstance(exc.code, int) else 1
    except Exception:
        err = traceback.format_exc()
        say("UNHANDLED ERROR:\n" + err)
        email_failure(err)
        exit_code = 1
    finally:
        # Push whatever the run produced — including the log line that explains a
        # failure. On a failed run the baselines were never rewritten, so only
        # the log (and any report already written) goes back up.
        if sync is not None:
            try:
                sync.push(keep_backups=KEEP_BACKUPS,
                          keep_report_prefixes=[f"plan_changes_{s['key']}_" for s in SOURCES],
                          keep_reports=KEEP_REPORTS,
                          only=None if GDRIVE_SYNC_EXTRAS else [s["baseline"] for s in SOURCES])
            except Exception:
                err = traceback.format_exc()
                say("Drive: upload back to Drive FAILED:\n" + err)
                # Worth its own alert: the email went out but the Drive baseline
                # did not move, so tomorrow's run will repeat today's list.
                email_failure("Upload back to Google Drive failed after the run. The baseline "
                              "in Drive was NOT updated, so the next run will report the same "
                              "changes again.\n\n" + err)
                exit_code = exit_code or 1
    sys.exit(exit_code)


# =============================================================================
#  One-off helpers:  python main.py get-token   |   python main.py check-token
# =============================================================================

def ask(name, prompt):
    return os.getenv(name) or input(prompt).strip()


# One token, two permissions: Drive (this job) and Gmail send (so the same
# token can replace the Gmail-only one in other scripts). Add more with the
# EXTRA_SCOPES environment variable, space-separated.
SCOPES = ["https://www.googleapis.com/auth/drive",
          "https://www.googleapis.com/auth/gmail.send"]
SCOPES += os.getenv("EXTRA_SCOPES", "").split()
SCOPE = " ".join(SCOPES)
# Must match an "Authorized redirect URI" on the OAuth client exactly. Set
# OAUTH_PORT to reuse one the client already has, e.g. http://localhost:8080/.
PORT = int(os.getenv("OAUTH_PORT", "8765"))
REDIRECT = f"http://localhost:{PORT}/"



def cmd_get_token():
    client_id = ask("GDRIVE_CLIENT_ID", "OAuth client id: ")
    client_secret = ask("GDRIVE_CLIENT_SECRET", "OAuth client secret: ")
    state = secrets.token_urlsafe(16)
    got = {}

    class Handler(http.server.BaseHTTPRequestHandler):
        def do_GET(self):
            q = urllib.parse.parse_qs(urllib.parse.urlparse(self.path).query)
            self.send_response(200)
            self.send_header("Content-Type", "text/html; charset=utf-8")
            self.end_headers()
            if q.get("state", [""])[0] != state or "code" not in q:
                self.wfile.write(b"<h2>Something went wrong. Go back to the terminal.</h2>")
                got["error"] = q.get("error", ["no code returned"])[0]
            else:
                self.wfile.write(b"<h2>Done. You can close this tab and return to the terminal.</h2>")
                got["code"] = q["code"][0]
            threading.Thread(target=httpd.shutdown, daemon=True).start()

        def log_message(self, *_):
            pass

    httpd = http.server.HTTPServer(("localhost", PORT), Handler)
    url = "https://accounts.google.com/o/oauth2/v2/auth?" + urllib.parse.urlencode({
        "client_id": client_id, "redirect_uri": REDIRECT, "response_type": "code",
        "scope": SCOPE, "access_type": "offline", "prompt": "consent", "state": state})
    print("\nOpening your browser. Sign in as the account that owns the Drive folder and approve.")
    print("If nothing opens, paste this into a browser:\n\n" + url + "\n")
    webbrowser.open(url)
    httpd.serve_forever()

    if "code" not in got:
        sys.exit(f"Authorization failed: {got.get('error')}")

    r = requests.post("https://oauth2.googleapis.com/token", data={
        "code": got["code"], "client_id": client_id, "client_secret": client_secret,
        "redirect_uri": REDIRECT, "grant_type": "authorization_code"}, timeout=60)
    if r.status_code >= 400:
        sys.exit(f"Token exchange failed: {r.status_code} {r.text}")
    tok = r.json()
    refresh = tok.get("refresh_token")
    if not refresh:
        sys.exit("Google did not return a refresh token. Revoke the app at "
                 "myaccount.google.com/permissions and run this again.")

    # quick sanity check: can we see Drive, and which permissions did we get?
    me = requests.get("https://www.googleapis.com/drive/v3/about",
                      headers={"Authorization": f"Bearer {tok['access_token']}"},
                      params={"fields": "user(emailAddress)"}, timeout=30).json()
    print(f"\nAuthorized as: {me.get('user', {}).get('emailAddress', '?')}")
    print("Permissions on this token:")
    for s in (tok.get("scope") or SCOPE).split():
        print("  -", s)
    print()
    print("Add these as GitHub repository secrets (Settings > Secrets and variables > Actions):\n")
    print(f"  GDRIVE_CLIENT_ID      = {client_id}")
    print(f"  GDRIVE_CLIENT_SECRET  = {client_secret}")
    print(f"  GDRIVE_REFRESH_TOKEN  = {refresh}")
    print("\nGDRIVE_FOLDER_ID is the last part of the folder's URL in Drive:")
    print("  https://drive.google.com/drive/folders/<GDRIVE_FOLDER_ID>\n")
    print("Keep the refresh token private: it grants full access to this account's Drive.")



DRIVE_SCOPES = ("https://www.googleapis.com/auth/drive",
                "https://www.googleapis.com/auth/drive.file",
                "https://www.googleapis.com/auth/drive.readonly")


def cmd_check_token():
    client_id = ask("GDRIVE_CLIENT_ID", "OAuth client id: ")
    client_secret = ask("GDRIVE_CLIENT_SECRET", "OAuth client secret: ")
    refresh = ask("GDRIVE_REFRESH_TOKEN", "Refresh token to test: ")
    folder_id = ask("GDRIVE_FOLDER_ID", "Drive folder id (from the folder URL): ")

    print("\n1) Refreshing the token ...")
    r = requests.post("https://oauth2.googleapis.com/token", data={
        "grant_type": "refresh_token", "client_id": client_id,
        "client_secret": client_secret, "refresh_token": refresh}, timeout=60)
    if r.status_code >= 400:
        sys.exit(f"   FAILED: {r.status_code} {r.text}\n"
                 "   -> client id/secret and refresh token do not belong together, "
                 "or the token was revoked.")
    access = r.json()["access_token"]
    print("   OK")

    print("\n2) Permissions on this token:")
    info = requests.get("https://oauth2.googleapis.com/tokeninfo",
                        params={"access_token": access}, timeout=30).json()
    scopes = info.get("scope", "").split()
    for s in scopes:
        print("   -", s)
    print("   account:", info.get("email", "(not included)"))
    has_write = "https://www.googleapis.com/auth/drive" in scopes
    has_any = any(s in DRIVE_SCOPES for s in scopes)
    if not has_any:
        print("\n   -> No Drive permission at all. This is a Gmail-only token.")
    elif not has_write:
        print("\n   -> Drive permission is present but not the full one; the job needs "
              "'auth/drive' to replace the baseline files.")

    print("\n3) Listing the folder ...")
    r = requests.get("https://www.googleapis.com/drive/v3/files",
                     headers={"Authorization": f"Bearer {access}"},
                     params={"q": f"'{folder_id}' in parents and trashed = false",
                             "fields": "files(name,size,modifiedTime)", "pageSize": 100,
                             "supportsAllDrives": "true", "includeItemsFromAllDrives": "true"},
                     timeout=60)
    if r.status_code >= 400:
        print(f"   FAILED: {r.status_code} {r.json().get('error', {}).get('message', r.text[:200])}")
        print("\nVERDICT: this token cannot be used for Drive. Run `python main.py get-token` with the "
              "same client id and secret to get one that can.")
        sys.exit(1)
    files = r.json().get("files", [])
    for f in sorted(files, key=lambda f: f["name"]):
        mb = int(f.get("size") or 0) / 1024 / 1024
        print(f"   {f['name']:<45} {mb:6.1f} MB  {f.get('modifiedTime', '')[:16]}")
    names = {f["name"] for f in files}
    missing = [n for n in ("Geotab_Devices.csv", "Zenduit_Devices.csv") if n not in names]
    if missing:
        print(f"\n   WARNING: not found in this folder: {', '.join(missing)}")

    if has_write:
        print("\nVERDICT: this token works for Drive. Use it as GDRIVE_REFRESH_TOKEN.")
    else:
        print("\nVERDICT: can read but not write. Run `python main.py get-token` for a full Drive token.")




def cmd_zoho_token():
    """python main.py zoho-token <grant code>  -> prints a Zoho refresh token.

    Make the grant code at https://api-console.zoho.com : open the client used
    for Analytics (or create a "Self Client"), tab "Generate Code", scope
        ZohoCRM.modules.READ,ZohoCRM.coql.READ
    duration 10 minutes, then run this within those 10 minutes."""
    code = sys.argv[2] if len(sys.argv) > 2 else input("Grant code from api-console.zoho.com: ").strip()
    cid = ask("ZOHO_CLIENT_ID_CRM", "Zoho client id: ") if not CRM_ID else CRM_ID
    sec = ask("ZOHO_CLIENT_SECRET_CRM", "Zoho client secret: ") if not CRM_SECRET else CRM_SECRET
    r = requests.post("https://accounts.zoho.com/oauth/v2/token", data={
        "grant_type": "authorization_code", "client_id": cid, "client_secret": sec, "code": code}, timeout=60)
    body = r.json()
    if r.status_code >= 400 or "refresh_token" not in body:
        sys.exit(f"Token exchange failed: {r.status_code} {body}\n"
                 "Grant codes expire quickly - generate a fresh one and retry at once.")
    print("\nAdd this GitHub secret:\n")
    print(f"  ZOHO_CLIENT_REFRESH_TOKEN_CRM = {body['refresh_token']}")
    print("\n(scope granted: " + body.get("scope", "?") + ")")
    # sanity check
    try:
        at = body["access_token"]
        t = requests.post(f"{CRM_API}/coql", headers={"Authorization": f"Zoho-oauthtoken {at}"},
                          json={"select_query": "select Cancellation_ID from Cancellations order by id desc limit 1"},
                          timeout=60)
        print("CRM check:", "OK - can read Cancellations" if t.status_code in (200, 204)
              else f"FAILED {t.status_code} {t.text[:200]}")
    except Exception as exc:
        print("CRM check failed:", exc)


if __name__ == "__main__":
    cmd = sys.argv[1] if len(sys.argv) > 1 else ""
    if cmd in ("get-token", "get_token"):
        cmd_get_token()
    elif cmd in ("check-token", "check_token"):
        cmd_check_token()
    elif cmd in ("zoho-token", "zoho_token"):
        cmd_zoho_token()
    else:
        main()
