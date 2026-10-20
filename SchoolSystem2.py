"""
School Management System
=========================
A role-based desktop application (Admin / Teacher / Parent) built with
Tkinter and SQLite.

FEATURES
--------
- Three login roles: Admin, Teacher, and Parent. Every password box has a
  "Show" button: press and hold it to see what you typed, release to hide.
- Only the Admin can register Students, Teachers, and Parents (gender is
  recorded for all three). Parent phone numbers must be Ghana mobile
  numbers of exactly 10 digits (e.g. 0241234567).
- COURSES: the Admin maintains a course catalog and assigns each course
  to a teacher across three or more classes at once.
- GRADING: each grade is entered as a Class Score (out of 60, converted
  to /50) and an Exam Score (out of 100, converted to /50). The total
  (out of 100) is graded. Teachers can re-select any student/term they
  have graded to edit the scores, or delete the entry.
- CLASS TEACHERS: only a class's designated Class Teacher can compile and
  send the consolidated results slip (with the student's passport photo),
  take daily student attendance, and send announcements to that class's
  parents.
- TIMETABLES: the Admin builds a weekly timetable per class; class
  teachers and parents can view and print/export it.
- ANNOUNCEMENTS: the Admin (to anyone) and Class Teachers (to their own
  class) post announcements to the parent portal, optionally attaching a
  student's performance summary, and optionally send them by SMS.
- FEES: the Admin sets the fee for each CLASS and term (every student in
  the class is billed it) and records payments per student (with search);
  parents track fees owed and paid for their children on the portal.
- ATTENDANCE: teachers can clock in only between the clock-in opening
  time the Admin sets and 4:00 pm; the exact time is compared with the
  Admin's reporting time (On Time / Late). Class Teachers take daily
  student attendance; parents see their child's attendance.
- NETWORK SYNC: with school_sync_server.py running somewhere reachable,
  every change made in any copy of this app is pushed over the internet
  and pulled into all the others (login screen -> "Network Sync" button).

CLASSES SUPPORTED
------------------
Nursery, KG 1, KG 2, Class 1-6, JHS 1-3

DEFAULT ADMIN LOGIN (created automatically on first run)
----------------------------------------------------------
    username: admin
    password: admin123

EMAIL / SMS SETUP
------------------
Edit the SMTP_* constants below to send result slips / reset codes by
email, and the TWILIO_* constants to send announcement SMS messages
(Twilio's REST API via the standard library; no extra package). Both
fail gracefully with an on-screen note if left as placeholders.

REQUIREMENTS
------------
- Python 3.8+ with tkinter (Linux: `sudo apt install python3-tk`)
- Optional: Pillow (photo previews) and fpdf2 (PDF export; it pulls in
  Pillow, which also lets the results-slip PDF embed the passport photo).
- Network sync needs only the standard library here; the shared server
  is the separate stdlib-only file school_sync_server.py.
"""

import os
import re
import shutil
import sqlite3
import hashlib
import random
import smtplib
import ssl
import base64
import json
import queue
import threading
import uuid
import urllib.request
import urllib.parse
import urllib.error
from email.message import EmailMessage
from datetime import datetime, timedelta

import tkinter as tk
from tkinter import ttk, messagebox, filedialog, simpledialog

try:
    from PIL import Image, ImageTk
    PIL_AVAILABLE = True
except ImportError:
    PIL_AVAILABLE = False

try:
    from fpdf import FPDF
    from fpdf.enums import XPos, YPos
    PDF_AVAILABLE = True
except ImportError:
    PDF_AVAILABLE = False


# ----------------------------------------------------------------------
# Configuration
# ----------------------------------------------------------------------
DB_FILE = "school_system.db"
PHOTO_DIR = "student_photos"

CLASSES = [
    "Nursery", "KG 1", "KG 2",
    "Class 1", "Class 2", "Class 3", "Class 4", "Class 5", "Class 6",
    "JHS 1", "JHS 2", "JHS 3",
]
TERMS = ["First Term", "Second Term", "Third Term"]
ROLE_TABLE = {"Admin": "admins", "Teacher": "teachers", "Parent": "parents"}
MIN_CLASSES_PER_COURSE_ASSIGNMENT = 3

DAYS = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
PERIODS = [
    "Period 1 (8:00-8:45)", "Period 2 (8:45-9:30)", "Period 3 (9:30-10:15)",
    "Break (10:15-10:30)", "Period 4 (10:30-11:15)", "Period 5 (11:15-12:00)",
    "Period 6 (12:00-12:45)", "Period 7 (12:45-1:30)",
]

GENDERS = ["Male", "Female", "Other"]
PAYMENT_METHODS = ["Cash", "Mobile Money", "Bank Transfer", "Cheque", "Other"]
ATTENDANCE_STATUSES = ["Present", "Absent", "Late", "Excused"]

# Teacher clock-in rules (the two times below are editable by the Admin).
DEFAULT_REPORTING_TIME = "07:30"      # clocking in after this = Late
DEFAULT_ATTENDANCE_OPEN_TIME = "06:00"  # clock-in is unavailable before this
CLOCK_IN_CLOSING_TIME = "16:00"       # clock-in ends at 4:00 pm, always
REPORTING_TIME_KEY = "teacher_reporting_time"
ATTENDANCE_OPEN_KEY = "attendance_open_time"

# --- Edit these to enable real result-slip / reset-code / announcement emails
SMTP_SERVER = "smtp.gmail.com"
SMTP_PORT = 587
SMTP_EMAIL = "your_school_email@example.com"
SMTP_PASSWORD = "your_app_password"
SCHOOL_NAME = "FRANKO EDUCATIONAL SCHOOL"

# --- Edit these to enable real announcement SMS messages (via Twilio) -
TWILIO_ACCOUNT_SID = "your_twilio_account_sid"
TWILIO_AUTH_TOKEN = "your_twilio_auth_token"
TWILIO_FROM_NUMBER = "+10000000000"

# ----------------------------------------------------------------------
# Network sync metadata
# ----------------------------------------------------------------------
# (table, primary-key column, {foreign-key column: referenced table},
#  [natural unique keys used to recognise "the same record" created on two
#   devices at once]).  Order matters: parents come before their children.
SYNC_TABLES = [
    ("admins", "id", {}, [("username",)]),
    ("parents", "id", {}, [("username",)]),
    ("teachers", "id", {}, [("username",)]),
    ("courses", "id", {}, [("name",), ("code",)]),
    ("students", "id", {"parent_id": "parents"}, []),
    ("course_assignments", "id", {"teacher_id": "teachers", "course_id": "courses"},
     [("teacher_id", "course_id", "class_name")]),
    ("grades", "id", {"student_id": "students", "teacher_id": "teachers", "course_id": "courses"},
     [("student_id", "course_id", "term")]),
    ("timetable_entries", "id", {"course_id": "courses", "teacher_id": "teachers"},
     [("class_name", "day", "period")]),
    ("announcements", "id", {}, []),
    ("settings", "key", {}, []),
    ("class_fees", "id", {}, [("class_name", "term")]),
    ("fee_bills", "id", {"student_id": "students"}, [("student_id", "term")]),
    ("fee_payments", "id", {"student_id": "students"}, []),
    ("teacher_attendance", "id", {"teacher_id": "teachers"}, [("teacher_id", "date")]),
    ("student_attendance", "id", {"student_id": "students", "recorded_by": "teachers"},
     [("student_id", "date")]),
]
SYNC_META = {t: {"pk": pk, "fks": fks, "nks": nks, "order": i}
             for i, (t, pk, fks, nks) in enumerate(SYNC_TABLES)}
SYNC_BATCH_SIZE = 300
SYNC_MAX_PHOTO_BYTES = 3 * 1024 * 1024
SYNC_EPOCH = "1970-01-01T00:00:00.000Z"   # seeded defaults use this so real data always wins
SQL_NOW = "strftime('%Y-%m-%dT%H:%M:%fZ','now')"

os.makedirs(PHOTO_DIR, exist_ok=True)


# ----------------------------------------------------------------------
# Small shared UI helper: password box with a press-and-hold "Show" button
# ----------------------------------------------------------------------
def make_password_entry(parent, textvariable, width=25):
    """Return a frame holding a masked Entry plus a 'Show' button. Press and
    hold the button to reveal the password so it can be checked; releasing
    (or moving the pointer away) hides it again."""
    frame = ttk.Frame(parent)
    entry = ttk.Entry(frame, textvariable=textvariable, show="*", width=width)
    entry.pack(side="left")
    button = ttk.Button(frame, text="Show", width=6)
    button.pack(side="left", padx=(4, 0))

    def reveal(_event=None):
        entry.configure(show="")

    def conceal(_event=None):
        entry.configure(show="*")

    button.bind("<ButtonPress-1>", reveal)
    button.bind("<ButtonRelease-1>", conceal)
    button.bind("<Leave>", conceal)
    frame.entry = entry
    return frame


# ----------------------------------------------------------------------
# Utility functions
# ----------------------------------------------------------------------
def hash_password(raw: str) -> str:
    return hashlib.sha256(raw.encode("utf-8")).hexdigest()


def compute_grade(score: float):
    """Return (letter_grade, remark) for a numeric score out of 100."""
    if score >= 80:
        return "A", "Excellent"
    if score >= 70:
        return "B", "Very Good"
    if score >= 60:
        return "C", "Good"
    if score >= 50:
        return "D", "Credit"
    if score >= 40:
        return "E", "Pass"
    return "F", "Fail"


def convert_class_score(raw_out_of_60: float) -> float:
    """Class score is entered out of 60 and converted to a mark out of 50."""
    return (raw_out_of_60 / 60.0) * 50.0


def convert_exam_score(raw_out_of_100: float) -> float:
    """Exam score is entered out of 100 and converted to a mark out of 50."""
    return (raw_out_of_100 / 100.0) * 50.0


def generate_reset_code() -> str:
    return f"{random.randint(0, 999999):06d}"


# -- Ghana phone numbers ------------------------------------------------
PHONE_HELP = "10 digits, Ghana mobile, e.g. 0241234567"


def normalize_ghana_phone(raw):
    """Return the 10-digit local form (e.g. '0241234567') of a Ghana mobile
    number, or None if it isn't one. Accepts 0XXXXXXXXX, +233XXXXXXXXX and
    233XXXXXXXXX (spaces/dashes ignored). Ghana mobile numbers start 02x/05x."""
    if raw is None:
        return None
    digits = re.sub(r"[\s\-().]", "", str(raw))
    if digits.startswith("+233"):
        digits = "0" + digits[4:]
    elif digits.startswith("233") and len(digits) == 12:
        digits = "0" + digits[3:]
    return digits if re.fullmatch(r"0[25]\d{8}", digits) else None


def ghana_to_e164(raw):
    """'0241234567' -> '+233241234567' (the Ghana country code), else None."""
    local = normalize_ghana_phone(raw)
    return "+233" + local[1:] if local else None


def phone_key_ok(proposed: str) -> bool:
    """Entry key-validation: digits only, never more than 10 of them."""
    return proposed == "" or (proposed.isdigit() and len(proposed) <= 10)


# -- Email -----------------------------------------------------------------
def email_is_configured() -> bool:
    return not (SMTP_EMAIL.endswith("example.com") or SMTP_PASSWORD == "your_app_password")


def send_email(to_email: str, subject: str, body: str):
    """Send a plain-text email. Returns (success: bool, error_message: str | None)."""
    if not email_is_configured():
        return False, "SMTP is not configured (placeholder credentials still in the script)."
    try:
        msg = EmailMessage()
        msg["Subject"] = subject
        msg["From"] = SMTP_EMAIL
        msg["To"] = to_email
        msg.set_content(body)
        context = ssl.create_default_context()
        with smtplib.SMTP(SMTP_SERVER, SMTP_PORT) as server:
            server.starttls(context=context)
            server.login(SMTP_EMAIL, SMTP_PASSWORD)
            server.send_message(msg)
        return True, None
    except Exception as exc:
        return False, str(exc)


# -- SMS (Twilio REST API, standard library only) ---------------------------
def sms_is_configured() -> bool:
    return not (
        TWILIO_ACCOUNT_SID.startswith("your_")
        or TWILIO_AUTH_TOKEN.startswith("your_")
        or TWILIO_FROM_NUMBER == "+10000000000"
    )


def send_sms(to_phone: str, message: str):
    """Send an SMS. Ghana numbers given in local form (024...) are sent with
    the +233 country code. Returns (success, error_message | None)."""
    if not sms_is_configured():
        return False, "SMS is not configured (placeholder Twilio credentials still in the script)."
    to_phone = ghana_to_e164(to_phone) or (to_phone or "")
    if not to_phone:
        return False, "No phone number on file."
    try:
        url = f"https://api.twilio.com/2010-04-01/Accounts/{TWILIO_ACCOUNT_SID}/Messages.json"
        data = urllib.parse.urlencode(
            {"From": TWILIO_FROM_NUMBER, "To": to_phone, "Body": message}
        ).encode("utf-8")
        creds = base64.b64encode(f"{TWILIO_ACCOUNT_SID}:{TWILIO_AUTH_TOKEN}".encode()).decode()
        req = urllib.request.Request(url, data=data, method="POST")
        req.add_header("Authorization", f"Basic {creds}")
        req.add_header("Content-Type", "application/x-www-form-urlencoded")
        with urllib.request.urlopen(req, timeout=15) as resp:
            if 200 <= resp.status < 300:
                return True, None
            return False, f"Twilio returned HTTP {resp.status}"
    except urllib.error.HTTPError as exc:
        return False, f"Twilio error {exc.code}: {exc.read().decode(errors='ignore')[:200]}"
    except Exception as exc:
        return False, str(exc)


def get_teacher_classes(db, teacher: dict):
    """All classes a teacher is linked to: the class they're Class Teacher of,
    plus every class they have a course assignment in - sorted school-order."""
    rows = db.run(
        "SELECT DISTINCT class_name FROM course_assignments WHERE teacher_id=?",
        (teacher["id"],),
    ).fetchall()
    classes = {r[0] for r in rows}
    if teacher.get("assigned_class"):
        classes.add(teacher["assigned_class"])
    return sorted(classes, key=lambda c: CLASSES.index(c) if c in CLASSES else 99)


# -- Settings, class fees, attendance ------------------------------------------
def get_setting(db, key, default=None):
    row = db.run("SELECT value FROM settings WHERE key=?", (key,)).fetchone()
    return row[0] if row else default


def set_setting(db, key, value):
    db.run(
        "INSERT INTO settings (key, value) VALUES (?, ?) "
        "ON CONFLICT(key) DO UPDATE SET value=excluded.value",
        (key, value),
        commit=True,
    )


def get_class_fee(db, class_name, term):
    row = db.run(
        "SELECT amount_due FROM class_fees WHERE class_name=? AND term=?", (class_name, term)
    ).fetchone()
    return row[0] if row else None


def compute_fee_balance(db, student_id, term):
    """Return (amount_due, amount_paid, balance) for a student/term. The
    amount due is the fee the Admin set for the student's CLASS and term (an
    old per-student bill is only used when the class has no fee set)."""
    cls = db.run("SELECT student_class FROM students WHERE id=?", (student_id,)).fetchone()
    amount_due = get_class_fee(db, cls[0], term) if cls else None
    if amount_due is None:
        bill = db.run(
            "SELECT amount_due FROM fee_bills WHERE student_id=? AND term=?", (student_id, term)
        ).fetchone()
        amount_due = bill[0] if bill else 0.0
    paid = db.run(
        "SELECT COALESCE(SUM(amount_paid), 0) FROM fee_payments WHERE student_id=? AND term=?",
        (student_id, term),
    ).fetchone()[0]
    return amount_due, paid, amount_due - paid


def compute_attendance_status(clock_in_time_str, reporting_time_str):
    """Compare a clock-in time ('HH:MM' or 'HH:MM:SS') with the Admin's
    reporting time ('HH:MM') and return 'On Time' or 'Late'."""
    fmt_in = "%H:%M:%S" if len(clock_in_time_str) > 5 else "%H:%M"
    t_in = datetime.strptime(clock_in_time_str, fmt_in).time()
    t_report = datetime.strptime(reporting_time_str, "%H:%M").time()
    return "On Time" if t_in <= t_report else "Late"


def attendance_window_state(now, open_str, close_str=CLOCK_IN_CLOSING_TIME):
    """Where 'now' sits relative to the teacher clock-in window:
    'before' (not open yet), 'open', or 'after' (closed for the day)."""
    t = now.time().replace(microsecond=0)
    opens = datetime.strptime(open_str, "%H:%M").time()
    closes = datetime.strptime(close_str, "%H:%M").time()
    if t < opens:
        return "before"
    if t >= closes:
        return "after"
    return "open"


# ----------------------------------------------------------------------
# Results-slip helpers (shared by the Teacher and Parent dashboards)
# ----------------------------------------------------------------------
def compile_student_results(db, student_id, term):
    """Gather a student's consolidated results for one term, across every
    course/teacher, plus their average and overall grade."""
    student = db.run(
        "SELECT s.name, s.dob, s.student_class, s.hometown, s.photo_path, p.name, p.email "
        "FROM students s LEFT JOIN parents p ON s.parent_id = p.id WHERE s.id=?",
        (student_id,),
    ).fetchone()
    if not student:
        return None
    grade_rows = db.run(
        "SELECT subject, class_score_converted, exam_score_converted, score, grade, remark "
        "FROM grades WHERE student_id=? AND term=? ORDER BY subject",
        (student_id, term),
    ).fetchall()
    average = sum(r[3] for r in grade_rows) / len(grade_rows) if grade_rows else None
    overall_grade, overall_remark = compute_grade(average) if average is not None else (None, None)
    return {
        "name": student[0], "dob": student[1], "student_class": student[2], "hometown": student[3],
        "photo_path": student[4], "parent_name": student[5], "parent_email": student[6], "term": term,
        "grade_rows": grade_rows, "average": average,
        "overall_grade": overall_grade, "overall_remark": overall_remark,
    }


def build_slip_text(data: dict) -> str:
    lines = [
        SCHOOL_NAME, "STUDENT RESULTS SLIP", "=" * 66,
        f"Name:      {data['name']}",
        f"Class:     {data['student_class']}",
        f"DOB:       {data['dob'] or 'N/A'}",
        f"Hometown:  {data['hometown'] or 'N/A'}",
        f"Parent:    {data['parent_name'] or 'N/A'}",
        f"Term:      {data['term']}",
        "-" * 66,
        f"{'Subject':<18}{'Class/50':<10}{'Exam/50':<10}{'Total':<8}{'Grade':<7}{'Remark'}",
        "-" * 66,
    ]
    for subject, class_conv, exam_conv, total, grade, remark in data["grade_rows"]:
        class_str = f"{class_conv:.1f}" if class_conv is not None else "-"
        exam_str = f"{exam_conv:.1f}" if exam_conv is not None else "-"
        lines.append(f"{subject:<18}{class_str:<10}{exam_str:<10}{total:<8.1f}{grade:<7}{remark}")
    lines.append("-" * 66)
    if data["average"] is not None:
        lines += [
            f"Average score: {data['average']:.1f}",
            f"Overall grade: {data['overall_grade']} ({data['overall_remark']})",
        ]
    if data.get("photo_path"):
        lines.append(f"[Passport photo on file: {os.path.basename(data['photo_path'])} - see PDF version]")
    lines += ["=" * 66, f"Generated on {datetime.now().strftime('%Y-%m-%d %H:%M')}"]
    return "\n".join(lines)


def export_slip_pdf(path: str, data: dict):
    """Write a results slip to PDF, embedding the student's passport photo
    (if on file) top-right. Raises RuntimeError if fpdf2 isn't installed."""
    if not PDF_AVAILABLE:
        raise RuntimeError("fpdf2 is not installed. Run: pip install fpdf2")
    pdf = FPDF()
    pdf.add_page()
    pdf.set_font("Helvetica", "B", 16)
    pdf.cell(0, 10, text=SCHOOL_NAME, align="C", new_x=XPos.LMARGIN, new_y=YPos.NEXT)
    pdf.set_font("Helvetica", "B", 12)
    pdf.cell(0, 8, text="STUDENT RESULTS SLIP", align="C", new_x=XPos.LMARGIN, new_y=YPos.NEXT)
    pdf.ln(4)

    photo_path = data.get("photo_path")
    if photo_path and os.path.exists(photo_path):
        try:
            pdf.image(photo_path, x=168, y=10, w=28)
        except Exception:
            pass  # unreadable image: the rest of the slip still prints

    pdf.set_font("Helvetica", "", 11)
    for line in (
        f"Name: {data['name']}", f"Class: {data['student_class']}",
        f"DOB: {data['dob'] or 'N/A'}", f"Hometown: {data['hometown'] or 'N/A'}",
        f"Parent: {data['parent_name'] or 'N/A'}", f"Term: {data['term']}",
    ):
        pdf.cell(0, 7, text=line, new_x=XPos.LMARGIN, new_y=YPos.NEXT)
    pdf.ln(4)

    col_widths = [50, 24, 24, 20, 18, 50]
    pdf.set_font("Helvetica", "B", 10)
    for w, h in zip(col_widths, ["Subject", "Class/50", "Exam/50", "Total", "Grade", "Remark"]):
        pdf.cell(w, 8, text=h, border=1, new_x=XPos.RIGHT, new_y=YPos.TOP)
    pdf.ln(8)
    pdf.set_font("Helvetica", "", 10)
    for subject, class_conv, exam_conv, total, grade, remark in data["grade_rows"]:
        class_str = f"{class_conv:.1f}" if class_conv is not None else "-"
        exam_str = f"{exam_conv:.1f}" if exam_conv is not None else "-"
        for w, val in zip(col_widths, [subject, class_str, exam_str, f"{total:.1f}", grade, remark]):
            pdf.cell(w, 8, text=str(val), border=1, new_x=XPos.RIGHT, new_y=YPos.TOP)
        pdf.ln(8)

    pdf.ln(4)
    pdf.set_font("Helvetica", "B", 11)
    if data["average"] is not None:
        pdf.cell(0, 7, text=f"Average score: {data['average']:.1f}", new_x=XPos.LMARGIN, new_y=YPos.NEXT)
        pdf.cell(0, 7, text=f"Overall grade: {data['overall_grade']} ({data['overall_remark']})",
                 new_x=XPos.LMARGIN, new_y=YPos.NEXT)
    pdf.set_font("Helvetica", "", 9)
    pdf.cell(0, 7, text=f"Generated on {datetime.now().strftime('%Y-%m-%d %H:%M')}",
             new_x=XPos.LMARGIN, new_y=YPos.NEXT)
    pdf.output(path)


def open_slip_window(parent_widget, db, student_id, term, allow_email=False):
    """Preview a student's results slip in a Toplevel, with Save-as-.txt,
    Save-as-PDF, and (optionally) Email-to-Parent buttons."""
    data = compile_student_results(db, student_id, term)
    if not data:
        messagebox.showerror("Error", "Student record not found.")
        return
    if not data["grade_rows"]:
        messagebox.showinfo("No grades yet", f"No grades have been entered for {data['name']} in {term}.")
        return
    slip_text = build_slip_text(data)

    win = tk.Toplevel(parent_widget)
    win.title(f"Results Slip - {data['name']}")
    win.geometry("520x580")

    top_frame = ttk.Frame(win)
    top_frame.pack(fill="x", padx=10, pady=(10, 0))
    if PIL_AVAILABLE and data.get("photo_path") and os.path.exists(data["photo_path"]):
        try:
            img = Image.open(data["photo_path"])
            img.thumbnail((90, 90))
            photo_img = ImageTk.PhotoImage(img)
            photo_lbl = ttk.Label(top_frame, image=photo_img)
            photo_lbl.image = photo_img  # keep a reference
            photo_lbl.pack(side="right", padx=6)
        except Exception:
            pass

    text_widget = tk.Text(win, font=("Courier New", 10), wrap="word")
    text_widget.insert("1.0", slip_text)
    text_widget.config(state="disabled")
    text_widget.pack(fill="both", expand=True, padx=10, pady=10)

    btn_frame = ttk.Frame(win)
    btn_frame.pack(fill="x", padx=10, pady=(0, 10))

    def save_txt():
        path = filedialog.asksaveasfilename(
            defaultextension=".txt",
            initialfile=f"{data['name'].replace(' ', '_')}_{term.replace(' ', '_')}_results.txt",
            filetypes=[("Text file", "*.txt")],
        )
        if not path:
            return
        with open(path, "w", encoding="utf-8") as f:
            f.write(slip_text)
        messagebox.showinfo("Saved", f"Results slip saved to:\n{path}", parent=win)

    def save_pdf():
        if not PDF_AVAILABLE:
            messagebox.showwarning(
                "PDF export unavailable",
                "Install fpdf2 to export as PDF: pip install fpdf2\n\nYou can still save as a .txt file.",
                parent=win,
            )
            return
        path = filedialog.asksaveasfilename(
            defaultextension=".pdf",
            initialfile=f"{data['name'].replace(' ', '_')}_{term.replace(' ', '_')}_results.pdf",
            filetypes=[("PDF file", "*.pdf")],
        )
        if not path:
            return
        try:
            export_slip_pdf(path, data)
            messagebox.showinfo("Saved", f"Results slip saved to:\n{path}", parent=win)
        except Exception as exc:
            messagebox.showerror("PDF export failed", str(exc), parent=win)

    def email_slip():
        parent_email = data["parent_email"]
        if not parent_email:
            messagebox.showwarning("No email", "This student's parent has no email on file.", parent=win)
            return
        if not email_is_configured():
            messagebox.showwarning(
                "Email not configured",
                "SMTP_EMAIL / SMTP_PASSWORD are still placeholders at the top of the script.\n"
                "Edit those constants with a real account to enable sending.\n\n"
                "The slip can still be saved as a .txt or .pdf file.",
                parent=win,
            )
            return
        body = (
            f"Dear Parent/Guardian,\n\nPlease find below the results slip for {data['name']}.\n\n"
            f"{slip_text}\n\nRegards,\n{SCHOOL_NAME}"
        )
        sent, error = send_email(parent_email, f"{data['name']} - Results Slip ({SCHOOL_NAME})", body)
        if sent:
            messagebox.showinfo("Sent", f"Results slip emailed to {parent_email}.", parent=win)
        else:
            messagebox.showerror("Email failed", f"Could not send email:\n{error}", parent=win)

    ttk.Button(btn_frame, text="Save as .txt", command=save_txt).pack(side="left", padx=4)
    pdf_label = "Save as PDF" if PDF_AVAILABLE else "Save as PDF (install fpdf2)"
    ttk.Button(btn_frame, text=pdf_label, command=save_pdf).pack(side="left", padx=4)

    if allow_email:
        parent_email = data["parent_email"]
        ttk.Button(
            btn_frame, text=f"Email to Parent ({parent_email or 'no email on file'})",
            command=email_slip, state=("normal" if parent_email else "disabled"),
        ).pack(side="left", padx=4)

    ttk.Button(btn_frame, text="Close", command=win.destroy).pack(side="right", padx=4)


# ----------------------------------------------------------------------
# Timetable helpers (shared by Admin, Teacher, and Parent views)
# ----------------------------------------------------------------------
def get_timetable_grid(db, class_name):
    """Return {(day, period): (course_name, teacher_name)} for a class."""
    rows = db.run(
        "SELECT te.day, te.period, c.name, t.name FROM timetable_entries te "
        "LEFT JOIN courses c ON te.course_id = c.id "
        "LEFT JOIN teachers t ON te.teacher_id = t.id "
        "WHERE te.class_name=?",
        (class_name,),
    ).fetchall()
    return {(day, period): (course_name, teacher_name) for day, period, course_name, teacher_name in rows}


def format_timetable_cell(course_name, teacher_name, max_len=18):
    if not course_name:
        return "-"
    cell = course_name
    if teacher_name:
        cell += f" / {teacher_name.split()[0]}"
    if len(cell) > max_len:
        cell = cell[: max_len - 3] + "..."      # ASCII only: PDF core fonts can't draw the unicode ellipsis
    return cell


def build_timetable_text(class_name, grid):
    col_w = 16
    header = f"{'Period':<28}" + "".join(f"{d:<{col_w}}" for d in DAYS)
    lines = [SCHOOL_NAME, f"CLASS TIMETABLE - {class_name}", "=" * len(header), header, "-" * len(header)]
    for period in PERIODS:
        row = f"{period:<28}"
        for day in DAYS:
            course_name, teacher_name = grid.get((day, period), (None, None))
            row += f"{format_timetable_cell(course_name, teacher_name):<{col_w}}"
        lines.append(row)
    lines += ["=" * len(header), f"Generated on {datetime.now().strftime('%Y-%m-%d %H:%M')}"]
    return "\n".join(lines)


def export_timetable_pdf(path, class_name, grid):
    if not PDF_AVAILABLE:
        raise RuntimeError("fpdf2 is not installed. Run: pip install fpdf2")
    pdf = FPDF(orientation="L")
    pdf.add_page()
    pdf.set_font("Helvetica", "B", 16)
    pdf.cell(0, 10, text=SCHOOL_NAME, align="C", new_x=XPos.LMARGIN, new_y=YPos.NEXT)
    pdf.set_font("Helvetica", "B", 13)
    pdf.cell(0, 8, text=f"CLASS TIMETABLE - {class_name}", align="C", new_x=XPos.LMARGIN, new_y=YPos.NEXT)
    pdf.ln(4)

    period_col_w, day_col_w = 55, 30
    pdf.set_font("Helvetica", "B", 10)
    pdf.cell(period_col_w, 10, text="Period", border=1, align="C", new_x=XPos.RIGHT, new_y=YPos.TOP)
    for day in DAYS:
        pdf.cell(day_col_w, 10, text=day, border=1, align="C", new_x=XPos.RIGHT, new_y=YPos.TOP)
    pdf.ln(10)

    pdf.set_font("Helvetica", "", 8)
    for period in PERIODS:
        pdf.cell(period_col_w, 10, text=period, border=1, new_x=XPos.RIGHT, new_y=YPos.TOP)
        for day in DAYS:
            course_name, teacher_name = grid.get((day, period), (None, None))
            cell = format_timetable_cell(course_name, teacher_name, max_len=16)
            pdf.cell(day_col_w, 10, text=cell, border=1, align="C", new_x=XPos.RIGHT, new_y=YPos.TOP)
        pdf.ln(10)

    pdf.ln(4)
    pdf.cell(0, 6, text=f"Generated on {datetime.now().strftime('%Y-%m-%d %H:%M')}",
             new_x=XPos.LMARGIN, new_y=YPos.NEXT)
    pdf.output(path)


def open_timetable_window(parent_widget, db, class_name):
    grid = get_timetable_grid(db, class_name)
    text = build_timetable_text(class_name, grid)

    win = tk.Toplevel(parent_widget)
    win.title(f"Timetable - {class_name}")
    win.geometry("700x430")

    text_widget = tk.Text(win, font=("Courier New", 9), wrap="none")
    text_widget.insert("1.0", text)
    text_widget.config(state="disabled")
    text_widget.pack(fill="both", expand=True, padx=10, pady=10)

    btn_frame = ttk.Frame(win)
    btn_frame.pack(fill="x", padx=10, pady=(0, 10))

    def save_txt():
        path = filedialog.asksaveasfilename(
            defaultextension=".txt",
            initialfile=f"{class_name.replace(' ', '_')}_timetable.txt",
            filetypes=[("Text file", "*.txt")],
        )
        if not path:
            return
        with open(path, "w", encoding="utf-8") as f:
            f.write(text)
        messagebox.showinfo("Saved", f"Timetable saved to:\n{path}", parent=win)

    def save_pdf():
        if not PDF_AVAILABLE:
            messagebox.showwarning(
                "PDF export unavailable",
                "Install fpdf2: pip install fpdf2\n\nYou can still save as a .txt file.",
                parent=win,
            )
            return
        path = filedialog.asksaveasfilename(
            defaultextension=".pdf",
            initialfile=f"{class_name.replace(' ', '_')}_timetable.pdf",
            filetypes=[("PDF file", "*.pdf")],
        )
        if not path:
            return
        try:
            export_timetable_pdf(path, class_name, grid)
            messagebox.showinfo("Saved", f"Timetable saved to:\n{path}", parent=win)
        except Exception as exc:
            messagebox.showerror("PDF export failed", str(exc), parent=win)

    ttk.Button(btn_frame, text="Save as .txt", command=save_txt).pack(side="left", padx=4)
    pdf_label = "Save as PDF" if PDF_AVAILABLE else "Save as PDF (install fpdf2)"
    ttk.Button(btn_frame, text=pdf_label, command=save_pdf).pack(side="left", padx=4)
    ttk.Button(btn_frame, text="Close", command=win.destroy).pack(side="right", padx=4)


# ----------------------------------------------------------------------
# Announcement helpers
# ----------------------------------------------------------------------
def get_parent_phones_for_audience(db, audience_type, audience_value):
    """SMS-ready (+233...) numbers for the parents an announcement targets.
    Numbers that aren't valid Ghana mobiles are skipped; duplicates removed."""
    if audience_type == "all":
        rows = db.run("SELECT phone FROM parents WHERE phone IS NOT NULL AND phone != ''").fetchall()
    elif audience_type == "class":
        rows = db.run(
            "SELECT p.phone FROM parents p JOIN students s ON s.parent_id = p.id "
            "WHERE s.student_class=? AND p.phone IS NOT NULL AND p.phone != ''",
            (audience_value,),
        ).fetchall()
    else:  # a single student
        rows = db.run(
            "SELECT p.phone FROM parents p JOIN students s ON s.parent_id = p.id "
            "WHERE s.id=? AND p.phone IS NOT NULL AND p.phone != ''",
            (audience_value,),
        ).fetchall()
    out = []
    for (phone,) in rows:
        e164 = ghana_to_e164(phone)
        if e164 and e164 not in out:
            out.append(e164)
    return out


# ----------------------------------------------------------------------
# Database layer
# ----------------------------------------------------------------------
class Database:
    def __init__(self, db_file=DB_FILE):
        self.conn = sqlite3.connect(db_file)
        self.conn.execute("PRAGMA foreign_keys = ON")
        self._create_tables()
        self._migrate()
        self._install_sync_schema()
        self._seed_defaults()

    def _create_tables(self):
        self.conn.executescript(
            """
            CREATE TABLE IF NOT EXISTS admins (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                username TEXT NOT NULL UNIQUE,
                password_hash TEXT NOT NULL,
                email TEXT
            );

            CREATE TABLE IF NOT EXISTS password_resets (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                role TEXT NOT NULL,
                user_id INTEGER NOT NULL,
                code TEXT NOT NULL,
                expires_at TEXT NOT NULL
            );

            CREATE TABLE IF NOT EXISTS parents (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                name TEXT NOT NULL,
                email TEXT NOT NULL,
                phone TEXT,
                username TEXT UNIQUE,
                password_hash TEXT,
                gender TEXT
            );

            CREATE TABLE IF NOT EXISTS teachers (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                name TEXT NOT NULL,
                email TEXT,
                subject TEXT,
                username TEXT NOT NULL UNIQUE,
                password_hash TEXT NOT NULL,
                assigned_class TEXT,
                gender TEXT
            );

            CREATE TABLE IF NOT EXISTS courses (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                name TEXT NOT NULL UNIQUE,
                code TEXT NOT NULL UNIQUE
            );

            CREATE TABLE IF NOT EXISTS course_assignments (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                teacher_id INTEGER NOT NULL,
                course_id INTEGER NOT NULL,
                class_name TEXT NOT NULL,
                FOREIGN KEY (teacher_id) REFERENCES teachers(id) ON DELETE CASCADE,
                FOREIGN KEY (course_id) REFERENCES courses(id) ON DELETE CASCADE,
                UNIQUE(teacher_id, course_id, class_name)
            );

            CREATE TABLE IF NOT EXISTS students (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                name TEXT NOT NULL,
                dob TEXT,
                parent_id INTEGER,
                hometown TEXT,
                student_class TEXT NOT NULL,
                photo_path TEXT,
                gender TEXT,
                FOREIGN KEY (parent_id) REFERENCES parents(id) ON DELETE SET NULL
            );

            CREATE TABLE IF NOT EXISTS grades (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                student_id INTEGER NOT NULL,
                teacher_id INTEGER NOT NULL,
                course_id INTEGER NOT NULL,
                subject TEXT NOT NULL,
                term TEXT NOT NULL,
                class_score REAL,
                exam_score REAL,
                class_score_converted REAL,
                exam_score_converted REAL,
                score REAL NOT NULL,
                grade TEXT NOT NULL,
                remark TEXT NOT NULL,
                FOREIGN KEY (student_id) REFERENCES students(id) ON DELETE CASCADE,
                FOREIGN KEY (teacher_id) REFERENCES teachers(id) ON DELETE CASCADE,
                FOREIGN KEY (course_id) REFERENCES courses(id) ON DELETE CASCADE,
                UNIQUE(student_id, course_id, term)
            );

            CREATE TABLE IF NOT EXISTS timetable_entries (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                class_name TEXT NOT NULL,
                day TEXT NOT NULL,
                period TEXT NOT NULL,
                course_id INTEGER,
                teacher_id INTEGER,
                FOREIGN KEY (course_id) REFERENCES courses(id) ON DELETE SET NULL,
                FOREIGN KEY (teacher_id) REFERENCES teachers(id) ON DELETE SET NULL,
                UNIQUE(class_name, day, period)
            );

            CREATE TABLE IF NOT EXISTS announcements (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                sender_role TEXT NOT NULL,
                sender_name TEXT NOT NULL,
                audience_type TEXT NOT NULL,
                audience_value TEXT,
                title TEXT NOT NULL,
                body TEXT NOT NULL,
                created_at TEXT NOT NULL,
                sms_sent INTEGER NOT NULL DEFAULT 0
            );

            CREATE TABLE IF NOT EXISTS settings (
                key TEXT PRIMARY KEY,
                value TEXT
            );

            CREATE TABLE IF NOT EXISTS class_fees (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                class_name TEXT NOT NULL,
                term TEXT NOT NULL,
                amount_due REAL NOT NULL,
                created_at TEXT NOT NULL,
                UNIQUE(class_name, term)
            );

            CREATE TABLE IF NOT EXISTS fee_bills (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                student_id INTEGER NOT NULL,
                term TEXT NOT NULL,
                amount_due REAL NOT NULL,
                description TEXT,
                created_at TEXT NOT NULL,
                FOREIGN KEY (student_id) REFERENCES students(id) ON DELETE CASCADE,
                UNIQUE(student_id, term)
            );

            CREATE TABLE IF NOT EXISTS fee_payments (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                student_id INTEGER NOT NULL,
                term TEXT NOT NULL,
                amount_paid REAL NOT NULL,
                payment_date TEXT NOT NULL,
                method TEXT,
                note TEXT,
                recorded_by TEXT,
                FOREIGN KEY (student_id) REFERENCES students(id) ON DELETE CASCADE
            );

            CREATE TABLE IF NOT EXISTS teacher_attendance (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                teacher_id INTEGER NOT NULL,
                date TEXT NOT NULL,
                clock_in_time TEXT NOT NULL,
                status TEXT NOT NULL,
                FOREIGN KEY (teacher_id) REFERENCES teachers(id) ON DELETE CASCADE,
                UNIQUE(teacher_id, date)
            );

            CREATE TABLE IF NOT EXISTS student_attendance (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                student_id INTEGER NOT NULL,
                date TEXT NOT NULL,
                status TEXT NOT NULL,
                recorded_by INTEGER,
                FOREIGN KEY (student_id) REFERENCES students(id) ON DELETE CASCADE,
                FOREIGN KEY (recorded_by) REFERENCES teachers(id) ON DELETE SET NULL,
                UNIQUE(student_id, date)
            );
            """
        )
        self.conn.commit()

    def _migrate(self):
        """Bring a database created by an older version of this script up to
        date. Safe to run every startup."""
        for stmt in (
            "ALTER TABLE admins ADD COLUMN email TEXT",
            "ALTER TABLE parents ADD COLUMN username TEXT",
            "ALTER TABLE parents ADD COLUMN password_hash TEXT",
            "ALTER TABLE parents ADD COLUMN gender TEXT",
            "ALTER TABLE teachers ADD COLUMN gender TEXT",
            "ALTER TABLE students ADD COLUMN gender TEXT",
            "ALTER TABLE grades ADD COLUMN class_score REAL",
            "ALTER TABLE grades ADD COLUMN exam_score REAL",
            "ALTER TABLE grades ADD COLUMN class_score_converted REAL",
            "ALTER TABLE grades ADD COLUMN exam_score_converted REAL",
        ):
            try:
                self.conn.execute(stmt)
                self.conn.commit()
            except sqlite3.OperationalError:
                pass  # column already exists
        self._migrate_grades_table()

    def _migrate_grades_table(self):
        """Very old databases stored grades keyed by free-text subject only (no
        course catalog). Rebuild around course_id, auto-creating a course for
        any legacy subject that doesn't have one."""
        cols = [r[1] for r in self.conn.execute("PRAGMA table_info(grades)").fetchall()]
        if not cols or "course_id" in cols:
            return

        cur = self.conn.cursor()
        legacy_rows = cur.execute(
            "SELECT id, student_id, teacher_id, subject, term, score, grade, remark FROM grades"
        ).fetchall()
        for subject in {row[3] for row in legacy_rows}:
            code = ("".join(w[:3].upper() for w in subject.split()) or "GEN")[:10]
            cur.execute("INSERT OR IGNORE INTO courses (name, code) VALUES (?, ?)", (subject, code))
        self.conn.commit()

        cur.execute("ALTER TABLE grades RENAME TO grades_legacy")
        cur.execute(
            """
            CREATE TABLE grades (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                student_id INTEGER NOT NULL,
                teacher_id INTEGER NOT NULL,
                course_id INTEGER NOT NULL,
                subject TEXT NOT NULL,
                term TEXT NOT NULL,
                class_score REAL,
                exam_score REAL,
                class_score_converted REAL,
                exam_score_converted REAL,
                score REAL NOT NULL,
                grade TEXT NOT NULL,
                remark TEXT NOT NULL,
                FOREIGN KEY (student_id) REFERENCES students(id) ON DELETE CASCADE,
                FOREIGN KEY (teacher_id) REFERENCES teachers(id) ON DELETE CASCADE,
                FOREIGN KEY (course_id) REFERENCES courses(id) ON DELETE CASCADE,
                UNIQUE(student_id, course_id, term)
            )
            """
        )
        for _id, student_id, teacher_id, subject, term, score, grade, remark in legacy_rows:
            course_row = cur.execute("SELECT id FROM courses WHERE name=?", (subject,)).fetchone()
            if not course_row:
                continue
            cur.execute(
                "INSERT OR IGNORE INTO grades "
                "(student_id, teacher_id, course_id, subject, term, score, grade, remark) "
                "VALUES (?, ?, ?, ?, ?, ?, ?, ?)",
                (student_id, teacher_id, course_row[0], subject, term, score, grade, remark),
            )
        cur.execute("DROP TABLE grades_legacy")
        self.conn.commit()

    # ------------------------------------------------------------------
    # Network sync bookkeeping
    # ------------------------------------------------------------------
    def set_applying(self, flag: bool):
        """While True, the change-tracking triggers stay quiet (used when
        applying changes received from the server, and when seeding)."""
        self.conn.execute(
            "INSERT OR REPLACE INTO sync_meta (key, value) VALUES ('applying', ?)",
            ("1" if flag else "0",),
        )

    def _install_sync_schema(self):
        """Give every synced table a globally unique uid + updated_at, and
        install triggers that record each local insert/update/delete in
        sync_outbox so it can be pushed to the server. Safe on every start."""
        c = self.conn
        c.executescript(
            """
            CREATE TABLE IF NOT EXISTS sync_meta (key TEXT PRIMARY KEY, value TEXT);
            CREATE TABLE IF NOT EXISTS sync_outbox (
                table_name TEXT NOT NULL,
                uid TEXT NOT NULL,
                op TEXT NOT NULL,
                changed_at TEXT NOT NULL,
                PRIMARY KEY (table_name, uid)
            );
            """
        )
        self.set_applying(False)        # a crash mid-apply must never leave tracking off
        if c.execute("SELECT value FROM sync_meta WHERE key='device_id'").fetchone() is None:
            c.execute("INSERT INTO sync_meta (key, value) VALUES ('device_id', ?)", (uuid.uuid4().hex,))

        applying_off = "(SELECT value FROM sync_meta WHERE key='applying') = '0'"
        upsert_outbox = (
            "INSERT INTO sync_outbox (table_name, uid, op, changed_at) "
            "SELECT '{t}', uid, 'upsert', " + SQL_NOW + " FROM {t} WHERE rowid = NEW.rowid AND uid IS NOT NULL "
            "ON CONFLICT(table_name, uid) DO UPDATE SET op = excluded.op, changed_at = excluded.changed_at;"
        )
        for table, pk, _fks, _nks in SYNC_TABLES:
            for col in ("uid TEXT", "updated_at TEXT"):
                try:
                    c.execute(f"ALTER TABLE {table} ADD COLUMN {col}")
                except sqlite3.OperationalError:
                    pass
            c.execute(f"CREATE UNIQUE INDEX IF NOT EXISTS idx_{table}_uid ON {table}(uid)")

            uid_expr = "key" if pk == "key" else "lower(hex(randomblob(16)))"
            # Rows that existed before sync: give them a uid and queue them for upload.
            c.execute(f"UPDATE {table} SET uid = {uid_expr} WHERE uid IS NULL")
            c.execute(
                f"INSERT OR IGNORE INTO sync_outbox (table_name, uid, op, changed_at) "
                f"SELECT '{table}', uid, 'upsert', {SQL_NOW} FROM {table} WHERE updated_at IS NULL"
            )
            c.execute(f"UPDATE {table} SET updated_at = {SQL_NOW} WHERE updated_at IS NULL")

            uid_default = "COALESCE(uid, key)" if pk == "key" else "COALESCE(uid, lower(hex(randomblob(16))))"
            for suffix in ("ai", "au", "ad"):
                c.execute(f"DROP TRIGGER IF EXISTS sync_{table}_{suffix}")
            c.execute(
                f"""
                CREATE TRIGGER sync_{table}_ai AFTER INSERT ON {table}
                WHEN {applying_off}
                BEGIN
                    UPDATE {table} SET uid = {uid_default}, updated_at = {SQL_NOW} WHERE rowid = NEW.rowid;
                    {upsert_outbox.format(t=table)}
                END
                """
            )
            c.execute(
                f"""
                CREATE TRIGGER sync_{table}_au AFTER UPDATE ON {table}
                WHEN {applying_off} AND NEW.updated_at IS OLD.updated_at AND NEW.uid IS OLD.uid
                BEGIN
                    UPDATE {table} SET updated_at = {SQL_NOW} WHERE rowid = NEW.rowid;
                    {upsert_outbox.format(t=table)}
                END
                """
            )
            c.execute(
                f"""
                CREATE TRIGGER sync_{table}_ad AFTER DELETE ON {table}
                WHEN {applying_off} AND OLD.uid IS NOT NULL
                BEGIN
                    INSERT INTO sync_outbox (table_name, uid, op, changed_at)
                    VALUES ('{table}', OLD.uid, 'delete', {SQL_NOW})
                    ON CONFLICT(table_name, uid) DO UPDATE SET op = excluded.op, changed_at = excluded.changed_at;
                END
                """
            )
        c.commit()

    def _seed_defaults(self):
        """Create the default admin login and default attendance settings if
        missing. Seeded rows get the epoch timestamp and are NOT queued for
        upload, so a brand-new install can never overwrite real data (e.g. a
        changed admin password) that already lives on the server."""
        c = self.conn
        self.set_applying(True)
        try:
            if c.execute("SELECT COUNT(*) FROM admins").fetchone()[0] == 0:
                c.execute(
                    "INSERT INTO admins (username, password_hash, uid, updated_at) VALUES (?, ?, ?, ?)",
                    ("admin", hash_password("admin123"), uuid.uuid4().hex, SYNC_EPOCH),
                )
            for key, value in ((REPORTING_TIME_KEY, DEFAULT_REPORTING_TIME),
                               (ATTENDANCE_OPEN_KEY, DEFAULT_ATTENDANCE_OPEN_TIME)):
                if c.execute("SELECT 1 FROM settings WHERE key=?", (key,)).fetchone() is None:
                    c.execute(
                        "INSERT INTO settings (key, value, uid, updated_at) VALUES (?, ?, ?, ?)",
                        (key, value, key, SYNC_EPOCH),
                    )
        finally:
            self.set_applying(False)
            c.commit()

    def run(self, query, params=(), commit=False):
        cur = self.conn.cursor()
        cur.execute(query, params)
        if commit:
            self.conn.commit()
        return cur


# ----------------------------------------------------------------------
# Network sync engine
# ----------------------------------------------------------------------
def sync_http_request(base_url, api_key, method, path, payload=None, timeout=30):
    """One HTTP call to the sync server. Returns (status, parsed_json).
    Network-level failures (offline, DNS, timeout) raise."""
    url = base_url.rstrip("/") + path
    data = json.dumps(payload).encode("utf-8") if payload is not None else None
    req = urllib.request.Request(url, data=data, method=method)
    req.add_header("X-API-Key", api_key)
    if data is not None:
        req.add_header("Content-Type", "application/json")
    try:
        with urllib.request.urlopen(req, timeout=timeout) as resp:
            body = resp.read().decode("utf-8")
            return resp.status, (json.loads(body) if body else {})
    except urllib.error.HTTPError as exc:
        try:
            body = json.loads(exc.read().decode("utf-8"))
        except Exception:
            body = {"error": str(exc.reason)}
        return exc.code, body


class SyncManager:
    """Keeps this device's database in step with every other device through
    the shared sync server.

    * Every local change is recorded by triggers in `sync_outbox`.
    * A sync cycle PUSHES those changes (local integer ids are translated to
      global uids) and PULLS whatever other devices changed.
    * Conflicts: last writer wins (by updated_at). Two devices creating "the
      same" record at once (same username, same grade slot, ...) are merged
      into one; on an exact tie the lower uid wins, so all devices agree.
    The network call runs on a worker thread; all database work stays on the
    caller's (UI) thread, so no locking is needed."""

    MAX_CHAIN = 20

    def __init__(self, db, root=None, on_applied=None):
        self.db = db
        self.root = root
        self.on_applied = on_applied
        self._busy = False
        self._chain = 0
        self._timer = None
        self._queue = queue.Queue()
        self._columns_cache = {}
        self.state = "idle"          # idle | syncing | ok | error
        self.last_message = ""
        self.log_lines = []

    # -- small helpers -------------------------------------------------
    def _log(self, message):
        self.last_message = message
        self.log_lines.append(f"{datetime.now().strftime('%H:%M:%S')}  {message}")
        del self.log_lines[:-100]

    def _meta_get(self, key, default=None):
        row = self.db.conn.execute("SELECT value FROM sync_meta WHERE key=?", (key,)).fetchone()
        return row[0] if row and row[0] is not None else default

    def _meta_set(self, key, value):
        self.db.conn.execute("INSERT OR REPLACE INTO sync_meta (key, value) VALUES (?, ?)", (key, str(value)))
        self.db.conn.commit()

    def get_config(self):
        try:
            interval = int(self._meta_get("interval", "30"))
        except ValueError:
            interval = 30
        try:
            last_seq = int(self._meta_get("last_seq", "0"))
        except ValueError:
            last_seq = 0
        return {
            "url": self._meta_get("server_url", ""), "api_key": self._meta_get("api_key", ""),
            "enabled": self._meta_get("enabled", "0") == "1", "interval": max(10, interval),
            "last_seq": last_seq, "server_id": self._meta_get("server_id", ""),
            "device_id": self._meta_get("device_id", ""), "last_sync_at": self._meta_get("last_sync_at", ""),
        }

    def save_config(self, url, api_key, enabled, interval):
        url = (url or "").strip().rstrip("/")
        if url and not url.lower().startswith(("http://", "https://")):
            raise ValueError("The server address must start with http:// or https://")
        try:
            interval = int(interval)
        except (TypeError, ValueError):
            raise ValueError("The sync interval must be a whole number of seconds.")
        if interval < 10:
            raise ValueError("The sync interval must be at least 10 seconds.")
        old = self.get_config()
        if url != old["url"]:
            # A different server means a different history: start over against it.
            self._meta_set("server_id", "")
            self._meta_set("last_seq", "0")
        self._meta_set("server_url", url)
        self._meta_set("api_key", (api_key or "").strip())
        self._meta_set("enabled", "1" if enabled else "0")
        self._meta_set("interval", interval)
        self.reload_schedule()

    def is_configured(self):
        cfg = self.get_config()
        return bool(cfg["url"] and cfg["api_key"])

    def pending_count(self):
        return self.db.conn.execute("SELECT COUNT(*) FROM sync_outbox").fetchone()[0]

    def status_summary(self):
        cfg = self.get_config()
        if not self.is_configured():
            return "Sync: not set up"
        pending = self.pending_count()
        if self.state == "syncing":
            return "Sync: syncing..."
        if self.state == "error":
            return f"Sync: problem - {pending} change(s) waiting"
        if self.state == "ok":
            when = cfg["last_sync_at"][11:19] if cfg["last_sync_at"] else "-"
            return f"Sync: up to date ({when}), {pending} waiting"
        return "Sync: on" if cfg["enabled"] else "Sync: paused (manual)"

    # -- id <-> uid translation ------------------------------------------
    def _columns(self, table):
        if table not in self._columns_cache:
            self._columns_cache[table] = [r[1] for r in self.db.conn.execute(f"PRAGMA table_info({table})")]
        return self._columns_cache[table]

    def _id_to_uid(self, table, local_id):
        if local_id is None:
            return None
        row = self.db.conn.execute(f"SELECT uid FROM {table} WHERE id=?", (local_id,)).fetchone()
        return row[0] if row else None

    def _uid_to_id(self, table, uid):
        row = self.db.conn.execute(f"SELECT id FROM {table} WHERE uid=?", (uid,)).fetchone()
        return row[0] if row else None

    def _queue_outbox(self, table, uid, op):
        self.db.conn.execute(
            f"INSERT INTO sync_outbox (table_name, uid, op, changed_at) VALUES (?, ?, ?, {SQL_NOW}) "
            "ON CONFLICT(table_name, uid) DO UPDATE SET op = excluded.op, changed_at = excluded.changed_at",
            (table, uid, op),
        )

    def _mark_all_dirty(self):
        for table, _pk, _fks, _nks in SYNC_TABLES:
            self.db.conn.execute(
                f"INSERT INTO sync_outbox (table_name, uid, op, changed_at) "
                f"SELECT '{table}', uid, 'upsert', {SQL_NOW} FROM {table} WHERE uid IS NOT NULL "
                "ON CONFLICT(table_name, uid) DO UPDATE SET op = excluded.op, changed_at = excluded.changed_at"
            )
        self.db.conn.commit()

    def force_full_resync(self):
        self._meta_set("last_seq", "0")
        self._mark_all_dirty()
        self._log("Full re-sync requested: everything will be re-sent and re-fetched.")

    # -- building the push ------------------------------------------------
    def _serialize_row(self, table, uid):
        meta = SYNC_META[table]
        cur = self.db.conn.execute(f"SELECT * FROM {table} WHERE uid=?", (uid,))
        row = cur.fetchone()
        if row is None:
            return None
        rec = dict(zip([d[0] for d in cur.description], row))
        updated_at = rec.pop("updated_at")
        rec.pop("uid")
        if meta["pk"] == "id":
            rec.pop("id")
        for col, ref in meta["fks"].items():
            if rec.get(col) is not None:
                ref_uid = self._id_to_uid(ref, rec[col])
                if ref_uid is None:
                    return None          # dangling reference: nothing sensible to send
                rec[col] = ref_uid
        if table == "announcements" and rec.get("audience_type") == "student" and rec.get("audience_value"):
            try:
                ref_uid = self._id_to_uid("students", int(rec["audience_value"]))
            except ValueError:
                ref_uid = None
            if ref_uid is None:
                return None
            rec["audience_value"] = ref_uid
        if table == "students" and rec.get("photo_path"):
            path = rec["photo_path"]
            name = os.path.basename(path)
            rec["photo_path"] = name
            if os.path.isfile(path) and os.path.getsize(path) <= SYNC_MAX_PHOTO_BYTES:
                with open(path, "rb") as f:
                    rec["_photo"] = {"name": name, "b64": base64.b64encode(f.read()).decode("ascii")}
        return {"table": table, "uid": uid, "op": "upsert", "updated_at": updated_at, "data": rec}

    def _prepare(self):
        cfg = self.get_config()
        rows = self.db.conn.execute("SELECT table_name, uid, op, changed_at FROM sync_outbox").fetchall()

        def sort_key(r):
            order = SYNC_META[r[0]]["order"] if r[0] in SYNC_META else 999
            return (0, order, r[3]) if r[2] == "upsert" else (1, -order, r[3])

        rows.sort(key=sort_key)               # parents before children; deletes last
        rows = rows[:SYNC_BATCH_SIZE]
        changes, snapshot = [], []
        for table, uid, op, changed_at in rows:
            snapshot.append((table, uid, changed_at))
            if table not in SYNC_META:
                continue
            if op == "delete":
                changes.append({"table": table, "uid": uid, "op": "delete",
                                "updated_at": changed_at, "data": None})
            else:
                ser = self._serialize_row(table, uid)
                if ser:
                    changes.append(ser)
        payload = {"device_id": cfg["device_id"], "since_seq": cfg["last_seq"], "changes": changes}
        return payload, snapshot

    # -- applying a pull ----------------------------------------------------
    def _update_row(self, table, rowid, data, ts):
        if data:
            sets = ", ".join(f"{c}=?" for c in data)
            self.db.conn.execute(f"UPDATE {table} SET {sets}, updated_at=? WHERE rowid=?",
                                 (*data.values(), ts, rowid))
        else:
            self.db.conn.execute(f"UPDATE {table} SET updated_at=? WHERE rowid=?", (ts, rowid))

    def _insert_row(self, table, data, uid, ts):
        cols = list(data) + ["uid", "updated_at"]
        self.db.conn.execute(
            f"INSERT INTO {table} ({', '.join(cols)}) VALUES ({', '.join('?' for _ in cols)})",
            (*data.values(), uid, ts),
        )

    def _requeue_children(self, table, local_id):
        """A row's uid changed: re-send every row that points at it."""
        for child, meta in SYNC_META.items():
            for col, ref in meta["fks"].items():
                if ref == table:
                    for (child_uid,) in self.db.conn.execute(
                            f"SELECT uid FROM {child} WHERE {col}=?", (local_id,)).fetchall():
                        self._queue_outbox(child, child_uid, "upsert")

    def _merge_collision(self, table, found, uid, inc_ts, data):
        """The same logical record was created on two devices. Keep ONE row;
        the lowest uid becomes the shared identity, newest content wins."""
        rowid, local_uid, local_ts = found[0], found[1], found[2] or ""
        if uid < local_uid:
            self.db.conn.execute(f"UPDATE {table} SET uid=? WHERE rowid=?", (uid, rowid))
            self._queue_outbox(table, local_uid, "delete")
            self._requeue_children(table, rowid)
            # On an exact timestamp tie the record with the lower uid wins, so
            # every device makes the same choice and they converge.
            if inc_ts >= local_ts:
                self._update_row(table, rowid, data, inc_ts)
            else:
                self._queue_outbox(table, uid, "upsert")
        elif inc_ts > local_ts:
            self._update_row(table, rowid, data, inc_ts)
            self._queue_outbox(table, local_uid, "upsert")
        return "merged"

    def _apply_upsert(self, ch):
        table, uid, inc_ts = ch["table"], ch["uid"], ch["updated_at"]
        meta = SYNC_META.get(table)
        if not meta:
            return "error"
        data = dict(ch.get("data") or {})
        photo = data.pop("_photo", None)
        for col, ref in meta["fks"].items():
            if data.get(col) is not None:
                local_id = self._uid_to_id(ref, data[col])
                if local_id is None:
                    return "unresolved"
                data[col] = local_id
        if table == "announcements" and data.get("audience_type") == "student" and data.get("audience_value"):
            local_id = self._uid_to_id("students", data["audience_value"])
            if local_id is None:
                return "unresolved"
            data["audience_value"] = str(local_id)
        if table == "students":
            if isinstance(photo, dict) and photo.get("name") and photo.get("b64"):
                safe = os.path.basename(str(photo["name"]))
                if safe and not safe.startswith("."):
                    dest = os.path.join(PHOTO_DIR, safe)
                    try:
                        raw = base64.b64decode(photo["b64"])
                        if not os.path.isfile(dest) or os.path.getsize(dest) != len(raw):
                            with open(dest, "wb") as f:
                                f.write(raw)
                        data["photo_path"] = dest
                    except (OSError, ValueError):
                        pass
            elif data.get("photo_path"):
                data["photo_path"] = os.path.join(PHOTO_DIR, os.path.basename(str(data["photo_path"])))
        known = set(self._columns(table)) - {"uid", "updated_at"}
        if meta["pk"] == "id":
            known.discard("id")
        data = {k: v for k, v in data.items() if k in known}

        local = self.db.conn.execute(f"SELECT rowid, updated_at FROM {table} WHERE uid=?", (uid,)).fetchone()
        if local:
            if local[1] and local[1] >= inc_ts:
                return "noop"                   # ours is as new or newer
            self._update_row(table, local[0], data, inc_ts)
            return "updated"
        for nk in meta["nks"]:
            vals = [data.get(c) for c in nk]
            if any(v is None for v in vals):
                continue
            found = self.db.conn.execute(
                f"SELECT rowid, uid, updated_at FROM {table} WHERE " + " AND ".join(f"{c}=?" for c in nk),
                vals,
            ).fetchone()
            if found and found[1] != uid:
                return self._merge_collision(table, found, uid, inc_ts, data)
        self._insert_row(table, data, uid, inc_ts)
        return "inserted"

    def _apply_delete(self, ch):
        table, uid, inc_ts = ch["table"], ch["uid"], ch["updated_at"]
        if table not in SYNC_META:
            return "error"
        local = self.db.conn.execute(f"SELECT rowid, updated_at FROM {table} WHERE uid=?", (uid,)).fetchone()
        if not local:
            return "noop"
        if local[1] and local[1] > inc_ts:
            return "noop"                       # edited here after it was deleted elsewhere
        self.db.conn.execute(f"DELETE FROM {table} WHERE rowid=?", (local[0],))
        return "deleted"

    def _apply_changes(self, changes):
        stats = {"inserted": 0, "updated": 0, "deleted": 0, "merged": 0, "noop": 0,
                 "unresolved": 0, "error": 0}
        upserts = sorted((c for c in changes if c.get("op") == "upsert"),
                         key=lambda c: SYNC_META.get(c.get("table"), {"order": 999})["order"])
        deletes = sorted((c for c in changes if c.get("op") == "delete"),
                         key=lambda c: -SYNC_META.get(c.get("table"), {"order": 999})["order"])
        self.db.set_applying(True)
        try:
            pending, leftover = upserts, []
            for _attempt in range(2):           # second pass catches out-of-order parents
                leftover = []
                for ch in pending:
                    try:
                        status = self._apply_upsert(ch)
                    except sqlite3.Error as exc:
                        self._log(f"Skipped a {ch.get('table')} change: {exc}")
                        status = "error"
                    if status == "unresolved":
                        leftover.append(ch)
                    else:
                        stats[status] += 1
                if not leftover or len(leftover) == len(pending):
                    break
                pending = leftover
            stats["unresolved"] += len(leftover)
            for ch in deletes:
                try:
                    stats[self._apply_delete(ch)] += 1
                except sqlite3.Error as exc:
                    self._log(f"Skipped a {ch.get('table')} delete: {exc}")
                    stats["error"] += 1
            self.db.conn.commit()
        finally:
            self.db.set_applying(False)
            self.db.conn.commit()
        return stats

    # -- completing a cycle ---------------------------------------------------
    def _finish(self, snapshot, resp):
        """Called after the server accepted our push. Returns a result dict."""
        conn = self.db.conn
        for table, uid, changed_at in snapshot:     # forget only what we sent and is unchanged since
            conn.execute("DELETE FROM sync_outbox WHERE table_name=? AND uid=? AND changed_at=?",
                         (table, uid, changed_at))
        conn.commit()
        cfg = self.get_config()
        server_id = resp.get("server_id", "")
        if cfg["server_id"] and server_id != cfg["server_id"]:
            self._meta_set("server_id", server_id)
            self._meta_set("last_seq", "0")
            self._mark_all_dirty()
            self._log("The server's data was reset - re-uploading everything from this device.")
            return {"more": True, "pushed": len(snapshot), "stats": {}, "changed": 0}
        if not cfg["server_id"]:
            self._meta_set("server_id", server_id)
        stats = self._apply_changes(resp.get("changes", []))
        self._meta_set("last_seq", int(resp.get("next_seq", cfg["last_seq"])))
        self._meta_set("last_sync_at", datetime.now().strftime("%Y-%m-%dT%H:%M:%S"))
        changed = stats["inserted"] + stats["updated"] + stats["deleted"] + stats["merged"]
        more = bool(resp.get("has_more")) or self.pending_count() > 0
        return {"more": more, "pushed": len(snapshot), "stats": stats, "changed": changed}

    def _describe(self, result):
        s = result["stats"]
        text = f"Sent {result['pushed']}, received {result['changed']} change(s)"
        if s.get("unresolved"):
            text += f" ({s['unresolved']} waiting on missing parent records)"
        return text

    # -- synchronous run (used by tests and scripts) -----------------------------
    def sync_blocking(self, max_cycles=50):
        cfg = self.get_config()
        totals = {"pushed": 0, "changed": 0}
        for _ in range(max_cycles):
            payload, snapshot = self._prepare()
            status, body = sync_http_request(cfg["url"], cfg["api_key"], "POST", "/sync", payload)
            if status != 200:
                raise RuntimeError(f"Sync failed: HTTP {status} {body}")
            result = self._finish(snapshot, body)
            totals["pushed"] += result["pushed"]
            totals["changed"] += result["changed"]
            if not result["more"]:
                break
        self.state = "ok"
        return totals

    # -- background (UI-friendly) run ------------------------------------------------
    def sync_async(self):
        if self._busy or not self.is_configured():
            return False
        cfg = self.get_config()
        try:
            payload, snapshot = self._prepare()
        except Exception as exc:                 # never let a sync problem crash the app
            self.state = "error"
            self._log(f"Could not prepare changes: {exc}")
            return False
        self._busy = True
        self.state = "syncing"
        threading.Thread(target=self._worker, args=(cfg["url"], cfg["api_key"], payload, snapshot),
                         daemon=True).start()
        self._schedule_poll()
        return True

    def sync_now(self):
        if not self.is_configured():
            self._log("Sync is not set up yet (server address and API key needed).")
            return False
        self._chain = 0
        return self.sync_async()

    def _worker(self, url, key, payload, snapshot):
        try:
            status, body = sync_http_request(url, key, "POST", "/sync", payload)
            self._queue.put((snapshot, status, body, None))
        except Exception as exc:
            self._queue.put((snapshot, None, None, exc))

    def _schedule_poll(self):
        if self.root is not None:
            self.root.after(150, self._poll)

    def _poll(self):
        try:
            item = self._queue.get_nowait()
        except queue.Empty:
            self._schedule_poll()
            return
        self._handle_result(*item)

    def _handle_result(self, snapshot, status, body, exc):
        self._busy = False
        again = False
        if exc is not None:
            self.state = "error"
            self._log(f"Cannot reach the sync server (offline?): {exc}")
        elif status == 401:
            self.state = "error"
            self._log("The server rejected the API key. Check it in the Network Sync window on the login screen.")
        elif status != 200:
            self.state = "error"
            self._log(f"Server error {status}: {(body or {}).get('error', 'unknown')}")
        else:
            try:
                result = self._finish(snapshot, body)
            except Exception as exc2:
                self.state = "error"
                self._log(f"Sync failed while applying changes: {exc2}")
            else:
                self.state = "ok"
                self._log(self._describe(result))
                if result["changed"] and self.on_applied:
                    try:
                        self.on_applied()
                    except Exception:
                        pass
                again = result["more"] and self._chain < self.MAX_CHAIN
                self._chain = self._chain + 1 if again else 0
        if again:
            self.sync_async()

    # -- scheduling ----------------------------------------------------------------------
    def _arm(self, delay_ms):
        if self.root is None:
            return
        if self._timer is not None:
            try:
                self.root.after_cancel(self._timer)
            except Exception:
                pass
            self._timer = None
        cfg = self.get_config()
        if cfg["enabled"] and self.is_configured():
            self._timer = self.root.after(delay_ms, self._tick)

    def start_auto(self):
        self._arm(1500)                          # first sync shortly after start-up

    def reload_schedule(self):
        self._arm(self.get_config()["interval"] * 1000)

    def _tick(self):
        self._timer = None
        if not self._busy:
            self._chain = 0
            self.sync_async()
        self._arm(self.get_config()["interval"] * 1000)

    def test_connection(self, url=None, api_key=None):
        cfg = self.get_config()
        url = (url if url is not None else cfg["url"]).strip()
        api_key = (api_key if api_key is not None else cfg["api_key"]).strip()
        if not url or not api_key:
            return False, "Enter the server address and API key first."
        try:
            status, body = sync_http_request(url, api_key, "GET", "/health", timeout=8)
        except Exception as exc:
            return False, f"Cannot reach the server: {exc}"
        if status == 200:
            return True, "Connected - the server accepted the API key."
        if status == 401:
            return False, "The server is reachable but rejected the API key."
        return False, f"Unexpected reply from server (HTTP {status})."


# ----------------------------------------------------------------------
# Login screen
# ----------------------------------------------------------------------
class LoginFrame(ttk.Frame):
    def __init__(self, parent, controller):
        super().__init__(parent)
        self.controller = controller
        self.db = controller.db

        wrapper = ttk.Frame(self)
        wrapper.place(relx=0.5, rely=0.5, anchor="center")

        ttk.Label(wrapper, text=SCHOOL_NAME, font=("Segoe UI", 18, "bold")).grid(
            row=0, column=0, columnspan=2, pady=(0, 4)
        )
        ttk.Label(wrapper, text="School Management System", font=("Segoe UI", 11)).grid(
            row=1, column=0, columnspan=2, pady=(0, 20)
        )

        ttk.Label(wrapper, text="Login as:").grid(row=2, column=0, sticky="e", padx=6, pady=6)
        self.role_var = tk.StringVar(value="Admin")
        ttk.Combobox(
            wrapper, textvariable=self.role_var, values=["Admin", "Teacher", "Parent"],
            state="readonly", width=22,
        ).grid(row=2, column=1, padx=6, pady=6)

        ttk.Label(wrapper, text="Username:").grid(row=3, column=0, sticky="e", padx=6, pady=6)
        self.username_var = tk.StringVar()
        ttk.Entry(wrapper, textvariable=self.username_var, width=25).grid(row=3, column=1, padx=6, pady=6)

        ttk.Label(wrapper, text="Password:").grid(row=4, column=0, sticky="e", padx=6, pady=6)
        self.password_var = tk.StringVar()
        make_password_entry(wrapper, self.password_var, 25).grid(row=4, column=1, padx=6, pady=6, sticky="w")

        ttk.Button(wrapper, text="Login", command=self.attempt_login).grid(
            row=5, column=0, columnspan=2, pady=(16, 4), sticky="ew"
        )
        ttk.Button(
            wrapper, text="Forgot Password?",
            command=lambda: ForgotPasswordDialog(self, controller),
        ).grid(row=6, column=0, columnspan=2, pady=(2, 4))
        ttk.Button(
            wrapper, text="Network Sync (connect to the internet)",
            command=lambda: SyncDialog(self, controller.sync),
        ).grid(row=7, column=0, columnspan=2, pady=(2, 4))
        ttk.Label(
            wrapper, text="Default admin login — username: admin   password: admin123",
            foreground="#666666", font=("Segoe UI", 8),
        ).grid(row=8, column=0, columnspan=2, pady=(10, 0))

        self.bind_all("<Return>", lambda e: self.attempt_login())

    def attempt_login(self):
        role = self.role_var.get()
        username = self.username_var.get().strip()
        password = self.password_var.get()
        if not username or not password:
            messagebox.showerror("Login failed", "Please enter both username and password.")
            return
        hashed = hash_password(password)

        if role == "Admin":
            row = self.db.run(
                "SELECT id, username FROM admins WHERE username=? AND password_hash=?",
                (username, hashed),
            ).fetchone()
            if row:
                self.controller.current_user = {"role": "Admin", "id": row[0], "name": row[1]}
                self.controller.show_admin_dashboard()
                return
        elif role == "Teacher":
            row = self.db.run(
                "SELECT id, name, assigned_class FROM teachers WHERE username=? AND password_hash=?",
                (username, hashed),
            ).fetchone()
            if row:
                self.controller.current_user = {
                    "role": "Teacher", "id": row[0], "name": row[1], "assigned_class": row[2],
                }
                self.controller.show_teacher_dashboard()
                return
        else:  # Parent
            row = self.db.run(
                "SELECT id, name FROM parents WHERE username=? AND password_hash=?",
                (username, hashed),
            ).fetchone()
            if row:
                self.controller.current_user = {"role": "Parent", "id": row[0], "name": row[1]}
                self.controller.show_parent_dashboard()
                return

        messagebox.showerror("Login failed", "Invalid username or password.")


# ----------------------------------------------------------------------
# Password reset dialogs (used by Admins, Teachers, and Parents)
# ----------------------------------------------------------------------
def _lookup_account(db, role, username):
    """Return (id, name, email, password_hash) for the given role/username, or None."""
    table = ROLE_TABLE[role]
    name_col = "username" if role == "Admin" else "name"
    return db.run(
        f"SELECT id, {name_col}, email, password_hash FROM {table} WHERE username=?",
        (username,),
    ).fetchone()


class ForgotPasswordDialog(tk.Toplevel):
    """Two-step 'forgot password' flow: request a code by email, then use the
    code to set a new password. Works for Admin, Teacher, and Parent accounts."""

    RESET_VALID_MINUTES = 15

    def __init__(self, parent, controller):
        super().__init__(parent)
        self.controller = controller
        self.db = controller.db
        self.title("Forgot Password")
        self.geometry("450x310")
        self.resizable(False, False)
        self.grab_set()

        self._step1_frame = ttk.Frame(self)
        self._step2_frame = ttk.Frame(self)
        self._build_step1()
        self._step1_frame.pack(fill="both", expand=True, padx=16, pady=16)

    # -- step 1: request a code -----------------------------------
    def _build_step1(self):
        f = self._step1_frame
        ttk.Label(f, text="Request a reset code", font=("Segoe UI", 12, "bold")).grid(
            row=0, column=0, columnspan=2, pady=(0, 10)
        )
        ttk.Label(f, text="I am a:").grid(row=1, column=0, sticky="e", padx=4, pady=6)
        self.role_var = tk.StringVar(value="Admin")
        ttk.Combobox(f, textvariable=self.role_var, values=["Admin", "Teacher", "Parent"],
                     state="readonly", width=20).grid(row=1, column=1, padx=4, pady=6)

        ttk.Label(f, text="Username:").grid(row=2, column=0, sticky="e", padx=4, pady=6)
        self.username_var = tk.StringVar()
        ttk.Entry(f, textvariable=self.username_var, width=22).grid(row=2, column=1, padx=4, pady=6)

        ttk.Label(f, text="Email on file:").grid(row=3, column=0, sticky="e", padx=4, pady=6)
        self.email_var = tk.StringVar()
        ttk.Entry(f, textvariable=self.email_var, width=22).grid(row=3, column=1, padx=4, pady=6)

        ttk.Button(f, text="Send Reset Code", command=self.request_code).grid(
            row=4, column=0, columnspan=2, pady=(16, 4)
        )
        ttk.Label(
            f, text="No email on file? Ask your Admin to reset it for you.",
            foreground="#666666", font=("Segoe UI", 8), wraplength=320,
        ).grid(row=5, column=0, columnspan=2, pady=(6, 0))

    def request_code(self):
        role = self.role_var.get()
        username = self.username_var.get().strip()
        email = self.email_var.get().strip()
        if not username or not email:
            messagebox.showerror("Missing info", "Enter both username and email.", parent=self)
            return
        account = _lookup_account(self.db, role, username)
        if not account or not account[2] or account[2].strip().lower() != email.lower():
            messagebox.showerror(
                "Not found",
                "No matching account with that username and email.\n"
                "Double-check the details, or ask your Admin for help.",
                parent=self,
            )
            return
        user_id = account[0]
        code = generate_reset_code()
        expires_at = (datetime.now() + timedelta(minutes=self.RESET_VALID_MINUTES)).isoformat()
        self.db.run("DELETE FROM password_resets WHERE role=? AND user_id=?", (role, user_id), commit=True)
        self.db.run(
            "INSERT INTO password_resets (role, user_id, code, expires_at) VALUES (?, ?, ?, ?)",
            (role, user_id, code, expires_at),
            commit=True,
        )
        sent, _error = send_email(
            email,
            f"{SCHOOL_NAME} - Password Reset Code",
            f"Your password reset code is: {code}\n\n"
            f"This code expires in {self.RESET_VALID_MINUTES} minutes.\n"
            "If you did not request this, you can ignore this email.",
        )
        self._role, self._user_id = role, user_id
        self._step1_frame.pack_forget()
        self._build_step2(show_code_fallback=None if sent else code)
        self._step2_frame.pack(fill="both", expand=True, padx=16, pady=16)
        if sent:
            messagebox.showinfo("Code sent", f"A reset code was emailed to {email}.", parent=self)

    # -- step 2: enter code + new password --------------------------
    def _build_step2(self, show_code_fallback=None):
        f = self._step2_frame
        for w in f.winfo_children():
            w.destroy()
        ttk.Label(f, text="Enter code & new password", font=("Segoe UI", 12, "bold")).grid(
            row=0, column=0, columnspan=2, pady=(0, 10)
        )
        if show_code_fallback:
            ttk.Label(
                f, text=(f"Email could not be sent (SMTP not configured).\n"
                         f"Your reset code is: {show_code_fallback}"),
                foreground="#b35900", wraplength=320, justify="left",
            ).grid(row=1, column=0, columnspan=2, pady=(0, 10))

        ttk.Label(f, text="Reset code:").grid(row=2, column=0, sticky="e", padx=4, pady=6)
        self.code_var = tk.StringVar()
        ttk.Entry(f, textvariable=self.code_var, width=22).grid(row=2, column=1, padx=4, pady=6)

        ttk.Label(f, text="New password:").grid(row=3, column=0, sticky="e", padx=4, pady=6)
        self.new_pw_var = tk.StringVar()
        make_password_entry(f, self.new_pw_var, 22).grid(row=3, column=1, padx=4, pady=6, sticky="w")

        ttk.Label(f, text="Confirm password:").grid(row=4, column=0, sticky="e", padx=4, pady=6)
        self.confirm_pw_var = tk.StringVar()
        make_password_entry(f, self.confirm_pw_var, 22).grid(row=4, column=1, padx=4, pady=6, sticky="w")

        ttk.Button(f, text="Reset Password", command=self.confirm_reset).grid(
            row=5, column=0, columnspan=2, pady=(16, 4)
        )

    def confirm_reset(self):
        code = self.code_var.get().strip()
        new_pw = self.new_pw_var.get()
        confirm_pw = self.confirm_pw_var.get()
        if not code or not new_pw:
            messagebox.showerror("Missing info", "Enter the code and a new password.", parent=self)
            return
        if new_pw != confirm_pw:
            messagebox.showerror("Mismatch", "Passwords do not match.", parent=self)
            return
        if len(new_pw) < 4:
            messagebox.showerror("Too short", "Password should be at least 4 characters.", parent=self)
            return
        row = self.db.run(
            "SELECT id, expires_at FROM password_resets WHERE role=? AND user_id=? AND code=?",
            (self._role, self._user_id, code),
        ).fetchone()
        if not row:
            messagebox.showerror("Invalid code", "That reset code is incorrect.", parent=self)
            return
        reset_id, expires_at = row
        if datetime.now().isoformat() > expires_at:
            messagebox.showerror("Expired", "That reset code has expired. Please request a new one.", parent=self)
            return
        table = ROLE_TABLE[self._role]
        self.db.run(
            f"UPDATE {table} SET password_hash=? WHERE id=?",
            (hash_password(new_pw), self._user_id),
            commit=True,
        )
        self.db.run("DELETE FROM password_resets WHERE id=?", (reset_id,), commit=True)
        messagebox.showinfo("Success", "Your password has been reset. You can now log in.", parent=self)
        self.destroy()


class ChangePasswordDialog(tk.Toplevel):
    """Self-service password (and email) change for an already logged-in user."""

    def __init__(self, parent, controller):
        super().__init__(parent)
        self.controller = controller
        self.db = controller.db
        self.user = controller.current_user
        self.title("Change Password")
        self.geometry("480x280")
        self.resizable(False, False)
        self.grab_set()

        table = ROLE_TABLE[self.user["role"]]
        row = self.db.run(f"SELECT email FROM {table} WHERE id=?", (self.user["id"],)).fetchone()
        current_email = row[0] if row and row[0] else ""

        frm = ttk.Frame(self)
        frm.pack(fill="both", expand=True, padx=16, pady=16)

        ttk.Label(frm, text=f"Account: {self.user['name']} ({self.user['role']})",
                  font=("Segoe UI", 10, "bold")).grid(row=0, column=0, columnspan=2, pady=(0, 10))

        ttk.Label(frm, text="Email (for password resets):").grid(row=1, column=0, sticky="e", padx=4, pady=6)
        self.email_var = tk.StringVar(value=current_email)
        ttk.Entry(frm, textvariable=self.email_var, width=22).grid(row=1, column=1, padx=4, pady=6)

        ttk.Label(frm, text="Current password:").grid(row=2, column=0, sticky="e", padx=4, pady=6)
        self.current_pw_var = tk.StringVar()
        make_password_entry(frm, self.current_pw_var, 22).grid(row=2, column=1, padx=4, pady=6, sticky="w")

        ttk.Label(frm, text="New password (optional):").grid(row=3, column=0, sticky="e", padx=4, pady=6)
        self.new_pw_var = tk.StringVar()
        make_password_entry(frm, self.new_pw_var, 22).grid(row=3, column=1, padx=4, pady=6, sticky="w")

        ttk.Label(frm, text="Confirm new password:").grid(row=4, column=0, sticky="e", padx=4, pady=6)
        self.confirm_pw_var = tk.StringVar()
        make_password_entry(frm, self.confirm_pw_var, 22).grid(row=4, column=1, padx=4, pady=6, sticky="w")

        ttk.Button(frm, text="Save", command=self.save).grid(row=5, column=0, columnspan=2, pady=(16, 4))

    def save(self):
        table = ROLE_TABLE[self.user["role"]]
        row = self.db.run(f"SELECT password_hash FROM {table} WHERE id=?", (self.user["id"],)).fetchone()
        if not row or hash_password(self.current_pw_var.get()) != row[0]:
            messagebox.showerror("Incorrect password", "Current password is incorrect.", parent=self)
            return

        new_pw = self.new_pw_var.get()
        if new_pw or self.confirm_pw_var.get():
            if new_pw != self.confirm_pw_var.get():
                messagebox.showerror("Mismatch", "New passwords do not match.", parent=self)
                return
            if len(new_pw) < 4:
                messagebox.showerror("Too short", "Password should be at least 4 characters.", parent=self)
                return

        email = self.email_var.get().strip()
        if new_pw:
            self.db.run(
                f"UPDATE {table} SET email=?, password_hash=? WHERE id=?",
                (email, hash_password(new_pw), self.user["id"]),
                commit=True,
            )
        else:
            self.db.run(f"UPDATE {table} SET email=? WHERE id=?", (email, self.user["id"]), commit=True)

        messagebox.showinfo("Saved", "Your account details have been updated.", parent=self)
        self.destroy()


# ----------------------------------------------------------------------
# Shared top bar used by every dashboard
# ----------------------------------------------------------------------
class TopBar(ttk.Frame):
    def __init__(self, parent, controller, title_text):
        super().__init__(parent)
        self.controller = controller
        ttk.Label(self, text=title_text, font=("Segoe UI", 14, "bold")).pack(side="left", padx=10, pady=8)
        user = controller.current_user
        who = f"Logged in as {user['name']} ({user['role']})"
        ttk.Label(self, text=who, foreground="#555555").pack(side="left", padx=20)
        ttk.Button(self, text="Logout", command=controller.logout).pack(side="right", padx=10, pady=6)
        ttk.Button(
            self, text="Change Password",
            command=lambda: ChangePasswordDialog(self, controller),
        ).pack(side="right", padx=4, pady=6)



# ----------------------------------------------------------------------
# Small placeholder shown where a feature is locked for the current user
# ----------------------------------------------------------------------
class LockedTab(ttk.Frame):
    def __init__(self, parent, message):
        super().__init__(parent)
        ttk.Label(
            self, text=message, foreground="#b30000", wraplength=520, justify="left",
            font=("Segoe UI", 10),
        ).pack(padx=20, pady=30)

    # no-op hooks so dashboards can refresh every tab uniformly
    def refresh(self):
        pass

    def refresh_students(self):
        pass

    def refresh_history(self):
        pass


# ----------------------------------------------------------------------
# Announcements composer (Admin: anyone; Class Teacher: own class only)
# ----------------------------------------------------------------------
class AnnouncementsTab(ttk.Frame):
    """allowed_classes=None means the sender is an Admin who can message All
    Parents or any class/student. A list restricts the sender (a Class
    Teacher) to those classes and the students in them."""

    def __init__(self, parent, db, sender_role, sender_name, allowed_classes=None):
        super().__init__(parent)
        self.db = db
        self.sender_role = sender_role
        self.sender_name = sender_name
        self.allowed_classes = allowed_classes
        self._student_map = {}
        self._history_lookup = {}
        self._build_ui()
        self.refresh_students()
        self.refresh_history()

    def _build_ui(self):
        form = ttk.LabelFrame(self, text="Compose Announcement")
        form.pack(fill="x", padx=10, pady=8)

        ttk.Label(form, text="Title:").grid(row=0, column=0, sticky="e", padx=4, pady=4)
        self.title_var = tk.StringVar()
        ttk.Entry(form, textvariable=self.title_var, width=42).grid(
            row=0, column=1, columnspan=3, sticky="w", padx=4, pady=4
        )

        ttk.Label(form, text="Send to:").grid(row=1, column=0, sticky="e", padx=4, pady=4)
        mode_values = ["All Parents", "A Class", "A Student"] if self.allowed_classes is None else ["A Class", "A Student"]
        self.mode_var = tk.StringVar(value=mode_values[0])
        mode_combo = ttk.Combobox(form, textvariable=self.mode_var, values=mode_values, state="readonly", width=14)
        mode_combo.grid(row=1, column=1, sticky="w", padx=4, pady=4)
        mode_combo.bind("<<ComboboxSelected>>", self._on_mode_change)

        classes_avail = self.allowed_classes if self.allowed_classes is not None else CLASSES
        self.class_var = tk.StringVar(value=classes_avail[0] if self.allowed_classes else "")
        self.class_combo = ttk.Combobox(form, textvariable=self.class_var, values=classes_avail, state="readonly", width=16)
        self.class_combo.grid(row=1, column=2, sticky="w", padx=4, pady=4)

        self.student_var = tk.StringVar()
        self.student_combo = ttk.Combobox(form, textvariable=self.student_var, width=24, state="readonly")
        self.student_combo.grid(row=1, column=3, sticky="w", padx=4, pady=4)

        ttk.Label(form, text="Message:").grid(row=2, column=0, sticky="ne", padx=4, pady=4)
        self.body_text = tk.Text(form, width=58, height=6)
        self.body_text.grid(row=2, column=1, columnspan=3, sticky="w", padx=4, pady=4)

        self.attach_perf_var = tk.BooleanVar(value=False)
        ttk.Checkbutton(
            form, text="Attach this student's performance summary", variable=self.attach_perf_var
        ).grid(row=3, column=1, sticky="w", padx=4, pady=2)
        ttk.Label(form, text="Term:").grid(row=3, column=2, sticky="e", padx=4, pady=2)
        self.perf_term_var = tk.StringVar(value=TERMS[0])
        ttk.Combobox(form, textvariable=self.perf_term_var, values=TERMS, state="readonly", width=14).grid(
            row=3, column=3, sticky="w", padx=4, pady=2
        )

        self.sms_var = tk.BooleanVar(value=False)
        sms_text = "Also send via SMS to parents' phone numbers"
        if not sms_is_configured():
            sms_text += " (SMS not configured - will only post to portal)"
        ttk.Checkbutton(form, text=sms_text, variable=self.sms_var).grid(
            row=4, column=1, columnspan=3, sticky="w", padx=4, pady=2
        )

        ttk.Button(form, text="Send Announcement", command=self.send_announcement).grid(
            row=5, column=1, pady=10, sticky="w"
        )

        history_label = "Sent Announcements" + ("" if self.allowed_classes is None else " (yours)")
        ttk.Label(self, text=history_label, font=("Segoe UI", 10, "bold")).pack(anchor="w", padx=10)

        table_frame = ttk.Frame(self)
        table_frame.pack(fill="both", expand=True, padx=10, pady=8)
        cols = ("date", "title", "audience", "sms")
        self.tree = ttk.Treeview(table_frame, columns=cols, show="headings", selectmode="browse")
        for c, h, w in zip(cols, ["Date", "Title", "Audience", "SMS"], [140, 200, 170, 60]):
            self.tree.heading(c, text=h)
            self.tree.column(c, width=w, anchor="center")
        vsb = ttk.Scrollbar(table_frame, orient="vertical", command=self.tree.yview)
        self.tree.configure(yscrollcommand=vsb.set)
        self.tree.pack(side="left", fill="both", expand=True)
        vsb.pack(side="right", fill="y")
        self.tree.bind("<<TreeviewSelect>>", self.on_history_select)

        self.detail_var = tk.StringVar(value="")
        ttk.Label(self, textvariable=self.detail_var, wraplength=760, justify="left", foreground="#333333").pack(
            anchor="w", padx=10, pady=(0, 10)
        )
        self._on_mode_change()

    def _on_mode_change(self, _event=None):
        mode = self.mode_var.get()
        self.class_combo.configure(state=("readonly" if mode == "A Class" else "disabled"))
        self.student_combo.configure(state=("readonly" if mode == "A Student" else "disabled"))

    def refresh_students(self):
        if self.allowed_classes is None:
            rows = self.db.run("SELECT id, name, student_class FROM students ORDER BY name").fetchall()
        elif self.allowed_classes:
            placeholders = ",".join("?" for _ in self.allowed_classes)
            rows = self.db.run(
                f"SELECT id, name, student_class FROM students WHERE student_class IN ({placeholders}) ORDER BY name",
                tuple(self.allowed_classes),
            ).fetchall()
        else:
            rows = []
        self._student_map = {f"{name} ({cls})": sid for sid, name, cls in rows}
        self.student_combo["values"] = list(self._student_map.keys())

    def send_announcement(self):
        if self.allowed_classes is not None and not self.allowed_classes:
            messagebox.showerror("Not allowed", "Only the Admin and a Class Teacher can send announcements.")
            return
        title = self.title_var.get().strip()
        body = self.body_text.get("1.0", "end").strip()
        if not title or not body:
            messagebox.showerror("Validation error", "Title and message are both required.")
            return

        mode = self.mode_var.get()
        student_id = None
        if mode == "All Parents":
            if self.allowed_classes is not None:
                messagebox.showerror("Not allowed", "Only the Admin can message all parents.")
                return
            audience_type, audience_value, audience_label = "all", None, "All Parents"
        elif mode == "A Class":
            cls = self.class_var.get()
            if not cls:
                messagebox.showerror("Validation error", "Choose a class.")
                return
            if self.allowed_classes is not None and cls not in self.allowed_classes:
                messagebox.showerror("Not allowed", "You can only message the parents of your own class.")
                return
            audience_type, audience_value, audience_label = "class", cls, f"Class: {cls}"
        else:
            label = self.student_var.get()
            if not label:
                messagebox.showerror("Validation error", "Choose a student.")
                return
            student_id = self._student_map[label]
            audience_type, audience_value, audience_label = "student", str(student_id), f"Student: {label}"

        if mode == "A Student" and self.attach_perf_var.get():
            data = compile_student_results(self.db, student_id, self.perf_term_var.get())
            if data and data["grade_rows"]:
                summary = [f"\n\nPerformance Summary ({self.perf_term_var.get()}):"]
                for subject, _cc, _ec, total, grade, _remark in data["grade_rows"]:
                    summary.append(f"- {subject}: {total:.1f} ({grade})")
                summary.append(f"Average: {data['average']:.1f} (Overall: {data['overall_grade']})")
                body += "\n".join(summary)
            else:
                messagebox.showinfo(
                    "No grades yet",
                    "No grades are recorded for that student/term - sending without a performance summary.",
                )

        created_at = datetime.now().isoformat()
        cur = self.db.run(
            "INSERT INTO announcements (sender_role, sender_name, audience_type, audience_value, title, body, "
            "created_at, sms_sent) VALUES (?, ?, ?, ?, ?, ?, ?, 0)",
            (self.sender_role, self.sender_name, audience_type, audience_value, title, body, created_at),
            commit=True,
        )
        announcement_id = cur.lastrowid

        sms_summary = ""
        if self.sms_var.get():
            if not sms_is_configured():
                sms_summary = "\n\nSMS was not sent: Twilio credentials are still placeholders at the top of the script."
            else:
                phones = get_parent_phones_for_audience(self.db, audience_type, audience_value)
                if not phones:
                    sms_summary = "\n\nNo valid Ghana phone numbers on file for this audience - SMS not sent."
                else:
                    sent, failed = 0, 0
                    for phone in phones:
                        ok, _err = send_sms(phone, f"{SCHOOL_NAME}: {title}\n{body}")
                        if ok:
                            sent += 1
                        else:
                            failed += 1
                    if sent:
                        self.db.run("UPDATE announcements SET sms_sent=1 WHERE id=?", (announcement_id,), commit=True)
                    sms_summary = f"\n\nSMS sent to {sent} number(s)." + (f" {failed} failed." if failed else "")

        messagebox.showinfo("Announcement Sent", f"Posted to the parent portal as: {audience_label}.{sms_summary}")
        self.title_var.set("")
        self.body_text.delete("1.0", "end")
        self.attach_perf_var.set(False)
        self.sms_var.set(False)
        self.refresh_history()

    def refresh_history(self):
        for row in self.tree.get_children():
            self.tree.delete(row)
        base_query = (
            "SELECT a.id, a.created_at, a.title, a.audience_type, a.audience_value, a.sms_sent, a.body, s.name "
            "FROM announcements a LEFT JOIN students s "
            "ON a.audience_type='student' AND CAST(s.id AS TEXT) = a.audience_value"
        )
        if self.allowed_classes is None:
            rows = self.db.run(base_query + " ORDER BY a.created_at DESC").fetchall()
        else:
            rows = self.db.run(
                base_query + " WHERE a.sender_name=? AND a.sender_role=? ORDER BY a.created_at DESC",
                (self.sender_name, self.sender_role),
            ).fetchall()
        self._history_lookup = {}
        for aid, created_at, title, atype, avalue, sms_sent, body, student_name in rows:
            when = created_at[:16].replace("T", " ")
            if atype == "all":
                audience = "All Parents"
            elif atype == "class":
                audience = f"Class: {avalue}"
            else:
                audience = f"Student: {student_name or ('ID ' + str(avalue))}"
            iid = str(aid)
            self.tree.insert("", "end", iid=iid, values=(when, title, audience, "Yes" if sms_sent else "No"))
            self._history_lookup[iid] = body

    def on_history_select(self, _event=None):
        sel = self.tree.selection()
        if not sel:
            return
        self.detail_var.set(self._history_lookup.get(sel[0], ""))


# ----------------------------------------------------------------------
# Admin dashboard
# ----------------------------------------------------------------------
class AdminDashboard(ttk.Frame):
    def __init__(self, parent, controller):
        super().__init__(parent)
        self.controller = controller
        db = controller.db
        admin_name = controller.current_user["name"]

        TopBar(self, controller, "Admin Dashboard").pack(fill="x")

        notebook = ttk.Notebook(self)
        notebook.pack(fill="both", expand=True, padx=10, pady=10)

        self.students_tab = StudentsAdminTab(notebook, db)
        self.teachers_tab = TeachersAdminTab(notebook, db)
        self.parents_tab = ParentsAdminTab(notebook, db, on_change=self._on_parents_changed)
        self.courses_tab = CoursesAdminTab(notebook, db, on_change=self._on_courses_changed)
        self.assignments_tab = CourseAssignmentsAdminTab(notebook, db)
        self.timetable_tab = TimetableAdminTab(notebook, db)
        self.announcements_tab = AnnouncementsTab(notebook, db, "Admin", admin_name, allowed_classes=None)
        self.fees_tab = FeesAdminTab(notebook, db)
        self.attendance_tab = AttendanceAdminTab(notebook, db)

        notebook.add(self.students_tab, text="1. Register Student")
        notebook.add(self.teachers_tab, text="2. Teachers")
        notebook.add(self.parents_tab, text="3. Parents")
        notebook.add(self.courses_tab, text="4. Courses")
        notebook.add(self.assignments_tab, text="5. Course Assignments")
        notebook.add(self.timetable_tab, text="6. Timetable")
        notebook.add(self.announcements_tab, text="7. Announcements")
        notebook.add(self.fees_tab, text="8. Fees")
        notebook.add(self.attendance_tab, text="9. Attendance")

        notebook.bind("<<NotebookTabChanged>>", self._on_tab_changed)

    def _on_tab_changed(self, _event=None):
        self.students_tab.refresh_parent_list()
        self.students_tab.refresh()
        self.teachers_tab.refresh()
        self.parents_tab.refresh()
        self.courses_tab.refresh()
        self.assignments_tab.refresh_dropdowns()
        self.assignments_tab.refresh()
        self.timetable_tab.refresh_dropdowns()
        self.announcements_tab.refresh_students()
        self.announcements_tab.refresh_history()
        self.fees_tab.refresh_all()
        self.attendance_tab.load_settings()

    def refresh_all(self):
        """Called after a network sync brought in changes from other devices."""
        self._on_tab_changed()

    def _on_parents_changed(self):
        self.students_tab.refresh_parent_list()

    def _on_courses_changed(self):
        self.assignments_tab.refresh_dropdowns()
        self.timetable_tab.refresh_dropdowns()


# -- 1. Register Student tab --------------------------------------------
class StudentsAdminTab(ttk.Frame):
    def __init__(self, parent, db: Database):
        super().__init__(parent)
        self.db = db
        self.selected_id = None
        self.photo_source_path = None
        self._parent_map = {}
        self._build_ui()
        self.refresh_parent_list()
        self.refresh()

    def _build_ui(self):
        form = ttk.LabelFrame(self, text="Student details")
        form.pack(fill="x", padx=10, pady=8)

        ttk.Label(form, text="Full Name:").grid(row=0, column=0, sticky="e", padx=4, pady=4)
        self.name_var = tk.StringVar()
        ttk.Entry(form, textvariable=self.name_var, width=28).grid(row=0, column=1, padx=4, pady=4)

        ttk.Label(form, text="Date of Birth (YYYY-MM-DD):").grid(row=0, column=2, sticky="e", padx=4, pady=4)
        self.dob_var = tk.StringVar()
        ttk.Entry(form, textvariable=self.dob_var, width=20).grid(row=0, column=3, padx=4, pady=4)

        ttk.Label(form, text="Parent:").grid(row=1, column=0, sticky="e", padx=4, pady=4)
        self.parent_var = tk.StringVar()
        self.parent_combo = ttk.Combobox(form, textvariable=self.parent_var, width=26, state="readonly")
        self.parent_combo.grid(row=1, column=1, padx=4, pady=4)

        ttk.Label(form, text="Hometown:").grid(row=1, column=2, sticky="e", padx=4, pady=4)
        self.hometown_var = tk.StringVar()
        ttk.Entry(form, textvariable=self.hometown_var, width=20).grid(row=1, column=3, padx=4, pady=4)

        ttk.Label(form, text="Class:").grid(row=2, column=0, sticky="e", padx=4, pady=4)
        self.class_var = tk.StringVar()
        ttk.Combobox(form, textvariable=self.class_var, values=CLASSES, state="readonly", width=26).grid(
            row=2, column=1, padx=4, pady=4
        )

        ttk.Label(form, text="Gender:").grid(row=3, column=0, sticky="e", padx=4, pady=4)
        self.gender_var = tk.StringVar()
        ttk.Combobox(form, textvariable=self.gender_var, values=GENDERS, state="readonly", width=26).grid(
            row=3, column=1, padx=4, pady=4
        )

        ttk.Label(form, text="Passport Picture:").grid(row=2, column=2, sticky="e", padx=4, pady=4)
        photo_frame = ttk.Frame(form)
        photo_frame.grid(row=2, column=3, sticky="w", padx=4, pady=4)
        ttk.Button(photo_frame, text="Choose Photo...", command=self.choose_photo).pack(side="left")
        self.photo_filename_lbl = ttk.Label(photo_frame, text="No file selected", foreground="#666666")
        self.photo_filename_lbl.pack(side="left", padx=6)

        self.preview_lbl = ttk.Label(form, text="(photo preview)", relief="groove", width=16, anchor="center")
        self.preview_lbl.grid(row=0, column=4, rowspan=3, padx=10, pady=4, sticky="ns")
        if not PIL_AVAILABLE:
            self.preview_lbl.config(text="Install Pillow\nfor photo preview")

        btn_frame = ttk.Frame(self)
        btn_frame.pack(fill="x", padx=10, pady=(0, 8))
        ttk.Button(btn_frame, text="Register Student", command=self.add_student).pack(side="left", padx=4)
        ttk.Button(btn_frame, text="Update Selected", command=self.update_student).pack(side="left", padx=4)
        ttk.Button(btn_frame, text="Delete Selected", command=self.delete_student).pack(side="left", padx=4)
        ttk.Button(btn_frame, text="Clear Form", command=self.clear_form).pack(side="left", padx=4)

        search_frame = ttk.Frame(self)
        search_frame.pack(fill="x", padx=10)
        ttk.Label(search_frame, text="Search:").pack(side="left")
        self.search_var = tk.StringVar()
        self.search_var.trace_add("write", lambda *a: self.refresh())
        ttk.Entry(search_frame, textvariable=self.search_var, width=30).pack(side="left", padx=6)

        table_frame = ttk.Frame(self)
        table_frame.pack(fill="both", expand=True, padx=10, pady=8)
        cols = ("id", "name", "dob", "parent", "hometown", "class", "gender")
        self.tree = ttk.Treeview(table_frame, columns=cols, show="headings", selectmode="browse")
        headers = ["ID", "Name", "DOB", "Parent", "Hometown", "Class", "Gender"]
        widths = [40, 150, 95, 150, 110, 85, 70]
        for c, h, w in zip(cols, headers, widths):
            self.tree.heading(c, text=h)
            self.tree.column(c, width=w, anchor="center")
        vsb = ttk.Scrollbar(table_frame, orient="vertical", command=self.tree.yview)
        self.tree.configure(yscrollcommand=vsb.set)
        self.tree.pack(side="left", fill="both", expand=True)
        vsb.pack(side="right", fill="y")
        self.tree.bind("<<TreeviewSelect>>", self.on_row_select)

    def refresh_parent_list(self):
        rows = self.db.run("SELECT id, name, email FROM parents ORDER BY name").fetchall()
        self._parent_map = {f"{name} <{email}>": pid for pid, name, email in rows}
        self.parent_combo["values"] = list(self._parent_map.keys())

    def choose_photo(self):
        path = filedialog.askopenfilename(
            title="Choose passport picture",
            filetypes=[("Image files", "*.jpg *.jpeg *.png *.bmp *.gif"), ("All files", "*.*")],
        )
        if not path:
            return
        self.photo_source_path = path
        self.photo_filename_lbl.config(text=os.path.basename(path))
        self._show_preview(path)

    def _show_preview(self, path):
        if not PIL_AVAILABLE or not path or not os.path.exists(path):
            return
        try:
            img = Image.open(path)
            img.thumbnail((110, 110))
            self._preview_photo = ImageTk.PhotoImage(img)
            self.preview_lbl.config(image=self._preview_photo, text="")
        except Exception:
            self.preview_lbl.config(text="(preview failed)")

    def clear_form(self):
        self.selected_id = None
        self.name_var.set("")
        self.dob_var.set("")
        self.parent_var.set("")
        self.hometown_var.set("")
        self.class_var.set("")
        self.gender_var.set("")
        self.photo_source_path = None
        self.photo_filename_lbl.config(text="No file selected")
        self.preview_lbl.config(image="", text="(photo preview)" if PIL_AVAILABLE else "Install Pillow\nfor photo preview")
        if self.tree.selection():
            self.tree.selection_remove(self.tree.selection())

    def on_row_select(self, _event=None):
        sel = self.tree.selection()
        if not sel:
            return
        values = self.tree.item(sel[0], "values")
        self.selected_id = values[0]
        self.name_var.set(values[1])
        self.dob_var.set(values[2])
        self.parent_var.set("")
        row = self.db.run("SELECT parent_id FROM students WHERE id=?", (self.selected_id,)).fetchone()
        if row and row[0]:
            match = self.db.run("SELECT name, email FROM parents WHERE id=?", (row[0],)).fetchone()
            if match:
                self.parent_var.set(f"{match[0]} <{match[1]}>")
        self.hometown_var.set(values[4])
        self.class_var.set(values[5])
        self.gender_var.set(values[6])
        photo_row = self.db.run("SELECT photo_path FROM students WHERE id=?", (self.selected_id,)).fetchone()
        self.photo_source_path = None
        if photo_row and photo_row[0]:
            self.photo_filename_lbl.config(text=os.path.basename(photo_row[0]))
            self._show_preview(photo_row[0])
        else:
            self.photo_filename_lbl.config(text="No file selected")

    def _validate(self):
        if not self.name_var.get().strip():
            messagebox.showerror("Validation error", "Student name is required.")
            return False
        if not self.class_var.get():
            messagebox.showerror("Validation error", "Please select a class.")
            return False
        if not self.parent_var.get():
            messagebox.showerror(
                "Validation error",
                "Please select a parent. Register the parent first under the 'Parents' tab if needed.",
            )
            return False
        return True

    def _save_photo(self):
        """Copy the chosen photo into PHOTO_DIR and return its stored path (or None)."""
        if not self.photo_source_path:
            return None
        ext = os.path.splitext(self.photo_source_path)[1]
        safe_name = "".join(c for c in self.name_var.get() if c.isalnum()) or "student"
        stamp = datetime.now().strftime("%Y%m%d%H%M%S")
        dest = os.path.join(PHOTO_DIR, f"{safe_name}_{stamp}{ext}")
        try:
            shutil.copy(self.photo_source_path, dest)
            return dest
        except Exception as exc:
            messagebox.showwarning("Photo not saved", f"Could not copy photo: {exc}")
            return None

    def add_student(self):
        if not self._validate():
            return
        parent_id = self._parent_map.get(self.parent_var.get())
        photo_path = self._save_photo()
        self.db.run(
            "INSERT INTO students (name, dob, parent_id, hometown, student_class, photo_path, gender) "
            "VALUES (?, ?, ?, ?, ?, ?, ?)",
            (self.name_var.get().strip(), self.dob_var.get().strip(), parent_id,
             self.hometown_var.get().strip(), self.class_var.get(), photo_path, self.gender_var.get()),
            commit=True,
        )
        messagebox.showinfo("Success", "Student registered.")
        self.clear_form()
        self.refresh()

    def update_student(self):
        if not self.selected_id:
            messagebox.showwarning("No selection", "Select a student in the table first.")
            return
        if not self._validate():
            return
        parent_id = self._parent_map.get(self.parent_var.get())
        photo_path = self._save_photo()
        if photo_path is None:
            row = self.db.run("SELECT photo_path FROM students WHERE id=?", (self.selected_id,)).fetchone()
            photo_path = row[0] if row else None
        self.db.run(
            "UPDATE students SET name=?, dob=?, parent_id=?, hometown=?, student_class=?, photo_path=?, gender=? "
            "WHERE id=?",
            (self.name_var.get().strip(), self.dob_var.get().strip(), parent_id,
             self.hometown_var.get().strip(), self.class_var.get(), photo_path, self.gender_var.get(),
             self.selected_id),
            commit=True,
        )
        messagebox.showinfo("Success", "Student record updated.")
        self.clear_form()
        self.refresh()

    def delete_student(self):
        if not self.selected_id:
            messagebox.showwarning("No selection", "Select a student in the table first.")
            return
        if not messagebox.askyesno("Confirm", "Delete this student and all their grade records?"):
            return
        self.db.run("DELETE FROM students WHERE id=?", (self.selected_id,), commit=True)
        self.clear_form()
        self.refresh()

    def refresh(self):
        for row in self.tree.get_children():
            self.tree.delete(row)
        query = (
            "SELECT s.id, s.name, s.dob, COALESCE(p.name, '(none)'), s.hometown, s.student_class, "
            "COALESCE(s.gender, '') "
            "FROM students s LEFT JOIN parents p ON s.parent_id = p.id"
        )
        term = self.search_var.get().strip()
        params = ()
        if term:
            query += " WHERE s.name LIKE ? OR s.student_class LIKE ? OR p.name LIKE ?"
            params = tuple(f"%{term}%" for _ in range(3))
        query += " ORDER BY s.id DESC"
        for row in self.db.run(query, params).fetchall():
            self.tree.insert("", "end", values=row)


# -- 2. Teachers tab (registration + Class Teacher assignment) ----------
class TeachersAdminTab(ttk.Frame):
    def __init__(self, parent, db: Database):
        super().__init__(parent)
        self.db = db
        self.selected_id = None
        self._build_ui()
        self.refresh()

    def _build_ui(self):
        form = ttk.LabelFrame(self, text="Teacher details & Class Teacher assignment")
        form.pack(fill="x", padx=10, pady=8)

        ttk.Label(form, text="Full Name:").grid(row=0, column=0, sticky="e", padx=4, pady=4)
        self.name_var = tk.StringVar()
        ttk.Entry(form, textvariable=self.name_var, width=25).grid(row=0, column=1, padx=4, pady=4)

        ttk.Label(form, text="Email:").grid(row=0, column=2, sticky="e", padx=4, pady=4)
        self.email_var = tk.StringVar()
        ttk.Entry(form, textvariable=self.email_var, width=25).grid(row=0, column=3, padx=4, pady=4)

        ttk.Label(form, text="Class Teacher of (optional):").grid(row=1, column=0, sticky="e", padx=4, pady=4)
        self.class_var = tk.StringVar()
        ttk.Combobox(form, textvariable=self.class_var, values=[""] + CLASSES, state="readonly", width=23).grid(
            row=1, column=1, padx=4, pady=4
        )

        ttk.Label(form, text="Login Username:").grid(row=1, column=2, sticky="e", padx=4, pady=4)
        self.username_var = tk.StringVar()
        ttk.Entry(form, textvariable=self.username_var, width=25).grid(row=1, column=3, padx=4, pady=4)

        ttk.Label(form, text="Login Password:").grid(row=2, column=0, sticky="e", padx=4, pady=4)
        self.password_var = tk.StringVar()
        make_password_entry(form, self.password_var, 25).grid(row=2, column=1, padx=4, pady=4, sticky="w")

        ttk.Label(form, text="Gender:").grid(row=3, column=0, sticky="e", padx=4, pady=4)
        self.gender_var = tk.StringVar()
        ttk.Combobox(form, textvariable=self.gender_var, values=GENDERS, state="readonly", width=23).grid(
            row=3, column=1, padx=4, pady=4
        )

        ttk.Label(
            form,
            text="Courses this teacher teaches (and which classes) are set up\n"
                 "in the 'Course Assignments' tab — each needs 3+ classes.",
            foreground="#666666", font=("Segoe UI", 8), justify="left",
        ).grid(row=2, column=2, columnspan=2, sticky="w", padx=4, pady=4)

        btn_frame = ttk.Frame(self)
        btn_frame.pack(fill="x", padx=10, pady=(0, 8))
        ttk.Button(btn_frame, text="Register Teacher", command=self.add_teacher).pack(side="left", padx=4)
        ttk.Button(btn_frame, text="Update Selected", command=self.update_teacher).pack(side="left", padx=4)
        ttk.Button(btn_frame, text="Set as Class Teacher", command=self.assign_as_class_teacher).pack(side="left", padx=4)
        ttk.Button(btn_frame, text="Reset Password", command=self.reset_teacher_password).pack(side="left", padx=4)
        ttk.Button(btn_frame, text="Delete Selected", command=self.delete_teacher).pack(side="left", padx=4)
        ttk.Button(btn_frame, text="Clear Form", command=self.clear_form).pack(side="left", padx=4)

        search_frame = ttk.Frame(self)
        search_frame.pack(fill="x", padx=10)
        ttk.Label(search_frame, text="Search:").pack(side="left")
        self.search_var = tk.StringVar()
        self.search_var.trace_add("write", lambda *a: self.refresh())
        ttk.Entry(search_frame, textvariable=self.search_var, width=30).pack(side="left", padx=6)

        table_frame = ttk.Frame(self)
        table_frame.pack(fill="both", expand=True, padx=10, pady=8)
        cols = ("id", "name", "email", "username", "class_teacher_of", "gender")
        self.tree = ttk.Treeview(table_frame, columns=cols, show="headings", selectmode="browse")
        headers = ["ID", "Name", "Email", "Username", "Class Teacher Of", "Gender"]
        widths = [40, 150, 170, 120, 130, 70]
        for c, h, w in zip(cols, headers, widths):
            self.tree.heading(c, text=h)
            self.tree.column(c, width=w, anchor="center")
        vsb = ttk.Scrollbar(table_frame, orient="vertical", command=self.tree.yview)
        self.tree.configure(yscrollcommand=vsb.set)
        self.tree.pack(side="left", fill="both", expand=True)
        vsb.pack(side="right", fill="y")
        self.tree.bind("<<TreeviewSelect>>", self.on_row_select)

    def clear_form(self):
        self.selected_id = None
        for var in (self.name_var, self.email_var, self.class_var, self.username_var, self.password_var,
                    self.gender_var):
            var.set("")
        if self.tree.selection():
            self.tree.selection_remove(self.tree.selection())

    def on_row_select(self, _event=None):
        sel = self.tree.selection()
        if not sel:
            return
        values = self.tree.item(sel[0], "values")
        self.selected_id = values[0]
        self.name_var.set(values[1])
        self.email_var.set(values[2])
        self.username_var.set(values[3])
        self.class_var.set(values[4] if values[4] != "(none)" else "")
        self.password_var.set("")
        self.gender_var.set(values[5])

    def _validate(self, require_password=True):
        if not self.name_var.get().strip():
            messagebox.showerror("Validation error", "Teacher name is required.")
            return False
        if not self.username_var.get().strip():
            messagebox.showerror("Validation error", "A login username is required.")
            return False
        if require_password and not self.password_var.get():
            messagebox.showerror("Validation error", "A login password is required.")
            return False
        return True

    def _resolve_class_teacher(self, cls, exclude_id):
        """Return the class name to store as assigned_class (or None),
        resolving a conflict if another teacher already holds that role."""
        if not cls:
            return None
        existing = self.db.run(
            "SELECT id, name FROM teachers WHERE assigned_class=? AND id != ?",
            (cls, exclude_id or -1),
        ).fetchone()
        if not existing:
            return cls
        if messagebox.askyesno(
            "Already assigned",
            f"{existing[1]} is already the Class Teacher of {cls}.\n"
            f"Reassign this role to {self.name_var.get().strip() or 'this teacher'} instead?",
        ):
            self.db.run("UPDATE teachers SET assigned_class=NULL WHERE id=?", (existing[0],), commit=True)
            return cls
        return None

    def add_teacher(self):
        if not self._validate(require_password=True):
            return
        assigned_class = self._resolve_class_teacher(self.class_var.get(), None)
        try:
            self.db.run(
                "INSERT INTO teachers (name, email, subject, username, password_hash, assigned_class, gender) "
                "VALUES (?, ?, ?, ?, ?, ?, ?)",
                (self.name_var.get().strip(), self.email_var.get().strip(), "",
                 self.username_var.get().strip(), hash_password(self.password_var.get()), assigned_class,
                 self.gender_var.get()),
                commit=True,
            )
            messagebox.showinfo("Success", "Teacher registered.")
            self.clear_form()
            self.refresh()
        except sqlite3.IntegrityError:
            messagebox.showerror("Error", "That username is already taken.")

    def update_teacher(self):
        if not self.selected_id:
            messagebox.showwarning("No selection", "Select a teacher in the table first.")
            return
        if not self._validate(require_password=False):
            return
        assigned_class = self._resolve_class_teacher(self.class_var.get(), self.selected_id)
        password_clause = ""
        params = [self.name_var.get().strip(), self.email_var.get().strip(),
                  self.username_var.get().strip(), assigned_class, self.gender_var.get()]
        if self.password_var.get():
            password_clause = ", password_hash=?"
            params.append(hash_password(self.password_var.get()))
        params.append(self.selected_id)
        try:
            self.db.run(
                f"UPDATE teachers SET name=?, email=?, username=?, assigned_class=?, gender=?{password_clause} "
                f"WHERE id=?",
                tuple(params),
                commit=True,
            )
            messagebox.showinfo("Success", "Teacher record updated.")
            self.clear_form()
            self.refresh()
        except sqlite3.IntegrityError:
            messagebox.showerror("Error", "That username is already taken.")

    def assign_as_class_teacher(self):
        if not self.selected_id:
            messagebox.showwarning("No selection", "Select a teacher in the table first.")
            return
        cls = self.class_var.get()
        if not cls:
            messagebox.showerror("Validation error", "Choose a class in the dropdown first.")
            return
        resolved = self._resolve_class_teacher(cls, self.selected_id)
        if not resolved:
            return
        self.db.run("UPDATE teachers SET assigned_class=? WHERE id=?", (resolved, self.selected_id), commit=True)
        messagebox.showinfo("Assigned", f"{self.name_var.get() or 'Teacher'} set as Class Teacher of {resolved}.")
        self.refresh()

    def delete_teacher(self):
        if not self.selected_id:
            messagebox.showwarning("No selection", "Select a teacher in the table first.")
            return
        if not messagebox.askyesno("Confirm", "Delete this teacher? Their course assignments will also be removed."):
            return
        self.db.run("DELETE FROM teachers WHERE id=?", (self.selected_id,), commit=True)
        self.clear_form()
        self.refresh()

    def reset_teacher_password(self):
        """Admin-driven password reset: no old password needed."""
        if not self.selected_id:
            messagebox.showwarning("No selection", "Select a teacher in the table first.")
            return
        new_pw = simpledialog.askstring(
            "Reset Password", f"New password for {self.name_var.get() or 'this teacher'}:",
            show="*", parent=self,
        )
        if new_pw is None:
            return
        if len(new_pw) < 4:
            messagebox.showerror("Too short", "Password should be at least 4 characters.")
            return
        confirm_pw = simpledialog.askstring("Reset Password", "Confirm new password:", show="*", parent=self)
        if confirm_pw is None:
            return
        if new_pw != confirm_pw:
            messagebox.showerror("Mismatch", "Passwords do not match. Password not changed.")
            return
        self.db.run(
            "UPDATE teachers SET password_hash=? WHERE id=?",
            (hash_password(new_pw), self.selected_id),
            commit=True,
        )
        self.db.run("DELETE FROM password_resets WHERE role='Teacher' AND user_id=?",
                     (self.selected_id,), commit=True)
        messagebox.showinfo("Success", "Teacher's password has been reset.")

    def refresh(self):
        for row in self.tree.get_children():
            self.tree.delete(row)
        query = (
            "SELECT id, name, COALESCE(email,''), username, COALESCE(assigned_class, '(none)'), "
            "COALESCE(gender,'') FROM teachers"
        )
        term = self.search_var.get().strip()
        params = ()
        if term:
            query += " WHERE name LIKE ? OR username LIKE ? OR assigned_class LIKE ?"
            params = tuple(f"%{term}%" for _ in range(3))
        query += " ORDER BY id DESC"
        for row in self.db.run(query, params).fetchall():
            self.tree.insert("", "end", values=row)


# -- 3. Parents tab (registration + portal login) ------------------------
class ParentsAdminTab(ttk.Frame):
    def __init__(self, parent, db: Database, on_change=None):
        super().__init__(parent)
        self.db = db
        self.on_change = on_change
        self.selected_id = None
        self._build_ui()
        self.refresh()

    def _build_ui(self):
        form = ttk.LabelFrame(self, text="Parent / Guardian details & portal login")
        form.pack(fill="x", padx=10, pady=8)

        ttk.Label(form, text="Full Name:").grid(row=0, column=0, sticky="e", padx=4, pady=4)
        self.name_var = tk.StringVar()
        ttk.Entry(form, textvariable=self.name_var, width=25).grid(row=0, column=1, padx=4, pady=4)

        ttk.Label(form, text="Email (result slips & resets):").grid(row=0, column=2, sticky="e", padx=4, pady=4)
        self.email_var = tk.StringVar()
        ttk.Entry(form, textvariable=self.email_var, width=25).grid(row=0, column=3, padx=4, pady=4)

        ttk.Label(form, text="Phone (10 digits):").grid(row=1, column=0, sticky="e", padx=4, pady=4)
        self.phone_var = tk.StringVar()
        ttk.Entry(
            form, textvariable=self.phone_var, width=25, validate="key",
            validatecommand=(self.register(phone_key_ok), "%P"),     # digits only, max 10
        ).grid(row=1, column=1, padx=4, pady=4)

        ttk.Label(form, text="Portal Username:").grid(row=1, column=2, sticky="e", padx=4, pady=4)
        self.username_var = tk.StringVar()
        ttk.Entry(form, textvariable=self.username_var, width=25).grid(row=1, column=3, padx=4, pady=4)

        ttk.Label(form, text="Portal Password:").grid(row=2, column=0, sticky="e", padx=4, pady=4)
        self.password_var = tk.StringVar()
        make_password_entry(form, self.password_var, 25).grid(row=2, column=1, padx=4, pady=4, sticky="w")
        ttk.Label(form, text=PHONE_HELP + " (used for SMS)", foreground="#666666", font=("Segoe UI", 8)).grid(
            row=2, column=2, columnspan=2, sticky="w", padx=4, pady=4
        )

        ttk.Label(form, text="Gender:").grid(row=3, column=0, sticky="e", padx=4, pady=4)
        self.gender_var = tk.StringVar()
        ttk.Combobox(form, textvariable=self.gender_var, values=GENDERS, state="readonly", width=23).grid(
            row=3, column=1, padx=4, pady=4
        )

        btn_frame = ttk.Frame(self)
        btn_frame.pack(fill="x", padx=10, pady=(0, 8))
        ttk.Button(btn_frame, text="Register Parent", command=self.add_parent).pack(side="left", padx=4)
        ttk.Button(btn_frame, text="Update Selected", command=self.update_parent).pack(side="left", padx=4)
        ttk.Button(btn_frame, text="Reset Password", command=self.reset_parent_password).pack(side="left", padx=4)
        ttk.Button(btn_frame, text="Delete Selected", command=self.delete_parent).pack(side="left", padx=4)
        ttk.Button(btn_frame, text="Clear Form", command=self.clear_form).pack(side="left", padx=4)

        search_frame = ttk.Frame(self)
        search_frame.pack(fill="x", padx=10)
        ttk.Label(search_frame, text="Search:").pack(side="left")
        self.search_var = tk.StringVar()
        self.search_var.trace_add("write", lambda *a: self.refresh())
        ttk.Entry(search_frame, textvariable=self.search_var, width=30).pack(side="left", padx=6)

        table_frame = ttk.Frame(self)
        table_frame.pack(fill="both", expand=True, padx=10, pady=8)
        cols = ("id", "name", "email", "phone", "username", "gender")
        self.tree = ttk.Treeview(table_frame, columns=cols, show="headings", selectmode="browse")
        headers = ["ID", "Name", "Email", "Phone", "Username", "Gender"]
        widths = [40, 150, 180, 100, 110, 70]
        for c, h, w in zip(cols, headers, widths):
            self.tree.heading(c, text=h)
            self.tree.column(c, width=w, anchor="center")
        vsb = ttk.Scrollbar(table_frame, orient="vertical", command=self.tree.yview)
        self.tree.configure(yscrollcommand=vsb.set)
        self.tree.pack(side="left", fill="both", expand=True)
        vsb.pack(side="right", fill="y")
        self.tree.bind("<<TreeviewSelect>>", self.on_row_select)

    def clear_form(self):
        self.selected_id = None
        for var in (self.name_var, self.email_var, self.phone_var, self.username_var, self.password_var,
                    self.gender_var):
            var.set("")
        if self.tree.selection():
            self.tree.selection_remove(self.tree.selection())

    def on_row_select(self, _event=None):
        sel = self.tree.selection()
        if not sel:
            return
        values = self.tree.item(sel[0], "values")
        self.selected_id = values[0]
        self.name_var.set(values[1])
        self.email_var.set(values[2])
        self.phone_var.set(normalize_ghana_phone(values[3]) or values[3])
        self.username_var.set(values[4])
        self.password_var.set("")
        self.gender_var.set(values[5])

    def _validate(self, require_password=True):
        if not self.name_var.get().strip() or not self.email_var.get().strip():
            messagebox.showerror("Validation error", "Parent name and email are required.")
            return False
        if normalize_ghana_phone(self.phone_var.get()) is None:
            messagebox.showerror(
                "Invalid phone number",
                "The phone number must be a Ghana mobile number of exactly 10 digits "
                "starting with 02 or 05, e.g. 0241234567.",
            )
            return False
        if not self.username_var.get().strip():
            messagebox.showerror("Validation error", "A portal username is required so the parent can log in.")
            return False
        if require_password and not self.password_var.get():
            messagebox.showerror("Validation error", "A portal password is required.")
            return False
        return True

    def add_parent(self):
        if not self._validate(require_password=True):
            return
        try:
            self.db.run(
                "INSERT INTO parents (name, email, phone, username, password_hash, gender) "
                "VALUES (?, ?, ?, ?, ?, ?)",
                (self.name_var.get().strip(), self.email_var.get().strip(),
                 normalize_ghana_phone(self.phone_var.get()),
                 self.username_var.get().strip(), hash_password(self.password_var.get()), self.gender_var.get()),
                commit=True,
            )
            messagebox.showinfo("Success", "Parent registered.")
            self.clear_form()
            self.refresh()
            if self.on_change:
                self.on_change()
        except sqlite3.IntegrityError:
            messagebox.showerror("Error", "That username is already taken.")

    def update_parent(self):
        if not self.selected_id:
            messagebox.showwarning("No selection", "Select a parent in the table first.")
            return
        if not self._validate(require_password=False):
            return
        password_clause = ""
        params = [self.name_var.get().strip(), self.email_var.get().strip(),
                  normalize_ghana_phone(self.phone_var.get()),
                  self.username_var.get().strip(), self.gender_var.get()]
        if self.password_var.get():
            password_clause = ", password_hash=?"
            params.append(hash_password(self.password_var.get()))
        params.append(self.selected_id)
        try:
            self.db.run(
                f"UPDATE parents SET name=?, email=?, phone=?, username=?, gender=?{password_clause} WHERE id=?",
                tuple(params),
                commit=True,
            )
            messagebox.showinfo("Success", "Parent record updated.")
            self.clear_form()
            self.refresh()
            if self.on_change:
                self.on_change()
        except sqlite3.IntegrityError:
            messagebox.showerror("Error", "That username is already taken.")

    def reset_parent_password(self):
        if not self.selected_id:
            messagebox.showwarning("No selection", "Select a parent in the table first.")
            return
        new_pw = simpledialog.askstring(
            "Reset Password", f"New password for {self.name_var.get() or 'this parent'}:",
            show="*", parent=self,
        )
        if new_pw is None:
            return
        if len(new_pw) < 4:
            messagebox.showerror("Too short", "Password should be at least 4 characters.")
            return
        confirm_pw = simpledialog.askstring("Reset Password", "Confirm new password:", show="*", parent=self)
        if confirm_pw is None:
            return
        if new_pw != confirm_pw:
            messagebox.showerror("Mismatch", "Passwords do not match. Password not changed.")
            return
        self.db.run(
            "UPDATE parents SET password_hash=? WHERE id=?",
            (hash_password(new_pw), self.selected_id),
            commit=True,
        )
        self.db.run("DELETE FROM password_resets WHERE role='Parent' AND user_id=?",
                     (self.selected_id,), commit=True)
        messagebox.showinfo("Success", "Parent's password has been reset.")

    def delete_parent(self):
        if not self.selected_id:
            messagebox.showwarning("No selection", "Select a parent in the table first.")
            return
        if not messagebox.askyesno("Confirm", "Delete this parent record?"):
            return
        self.db.run("DELETE FROM parents WHERE id=?", (self.selected_id,), commit=True)
        self.clear_form()
        self.refresh()
        if self.on_change:
            self.on_change()

    def refresh(self):
        for row in self.tree.get_children():
            self.tree.delete(row)
        query = "SELECT id, name, email, COALESCE(phone,''), COALESCE(username,''), COALESCE(gender,'') FROM parents"
        term = self.search_var.get().strip()
        params = ()
        if term:
            query += " WHERE name LIKE ? OR email LIKE ? OR username LIKE ?"
            params = tuple(f"%{term}%" for _ in range(3))
        query += " ORDER BY id DESC"
        for row in self.db.run(query, params).fetchall():
            self.tree.insert("", "end", values=row)


# -- 4. Courses tab (course catalog) -------------------------------------
class CoursesAdminTab(ttk.Frame):
    def __init__(self, parent, db: Database, on_change=None):
        super().__init__(parent)
        self.db = db
        self.on_change = on_change
        self.selected_id = None
        self._build_ui()
        self.refresh()

    def _build_ui(self):
        form = ttk.LabelFrame(self, text="Course details")
        form.pack(fill="x", padx=10, pady=8)

        ttk.Label(form, text="Course Name:").grid(row=0, column=0, sticky="e", padx=4, pady=4)
        self.name_var = tk.StringVar()
        ttk.Entry(form, textvariable=self.name_var, width=28).grid(row=0, column=1, padx=4, pady=4)

        ttk.Label(form, text="Course Code:").grid(row=0, column=2, sticky="e", padx=4, pady=4)
        self.code_var = tk.StringVar()
        ttk.Entry(form, textvariable=self.code_var, width=15).grid(row=0, column=3, padx=4, pady=4)

        btn_frame = ttk.Frame(self)
        btn_frame.pack(fill="x", padx=10, pady=(0, 8))
        ttk.Button(btn_frame, text="Add Course", command=self.add_course).pack(side="left", padx=4)
        ttk.Button(btn_frame, text="Update Selected", command=self.update_course).pack(side="left", padx=4)
        ttk.Button(btn_frame, text="Delete Selected", command=self.delete_course).pack(side="left", padx=4)
        ttk.Button(btn_frame, text="Clear Form", command=self.clear_form).pack(side="left", padx=4)

        search_frame = ttk.Frame(self)
        search_frame.pack(fill="x", padx=10)
        ttk.Label(search_frame, text="Search:").pack(side="left")
        self.search_var = tk.StringVar()
        self.search_var.trace_add("write", lambda *a: self.refresh())
        ttk.Entry(search_frame, textvariable=self.search_var, width=30).pack(side="left", padx=6)

        table_frame = ttk.Frame(self)
        table_frame.pack(fill="both", expand=True, padx=10, pady=8)
        cols = ("id", "name", "code")
        self.tree = ttk.Treeview(table_frame, columns=cols, show="headings", selectmode="browse")
        for c, h, w in zip(cols, ["ID", "Course Name", "Code"], [50, 220, 100]):
            self.tree.heading(c, text=h)
            self.tree.column(c, width=w, anchor="center")
        vsb = ttk.Scrollbar(table_frame, orient="vertical", command=self.tree.yview)
        self.tree.configure(yscrollcommand=vsb.set)
        self.tree.pack(side="left", fill="both", expand=True)
        vsb.pack(side="right", fill="y")
        self.tree.bind("<<TreeviewSelect>>", self.on_row_select)

    def clear_form(self):
        self.selected_id = None
        self.name_var.set("")
        self.code_var.set("")
        if self.tree.selection():
            self.tree.selection_remove(self.tree.selection())

    def on_row_select(self, _event=None):
        sel = self.tree.selection()
        if not sel:
            return
        values = self.tree.item(sel[0], "values")
        self.selected_id = values[0]
        self.name_var.set(values[1])
        self.code_var.set(values[2])

    def _validate(self):
        if not self.name_var.get().strip() or not self.code_var.get().strip():
            messagebox.showerror("Validation error", "Course name and code are both required.")
            return False
        return True

    def add_course(self):
        if not self._validate():
            return
        try:
            self.db.run(
                "INSERT INTO courses (name, code) VALUES (?, ?)",
                (self.name_var.get().strip(), self.code_var.get().strip().upper()),
                commit=True,
            )
            messagebox.showinfo("Success", "Course added.")
            self.clear_form()
            self.refresh()
            if self.on_change:
                self.on_change()
        except sqlite3.IntegrityError:
            messagebox.showerror("Error", "A course with that name or code already exists.")

    def update_course(self):
        if not self.selected_id:
            messagebox.showwarning("No selection", "Select a course in the table first.")
            return
        if not self._validate():
            return
        try:
            self.db.run(
                "UPDATE courses SET name=?, code=? WHERE id=?",
                (self.name_var.get().strip(), self.code_var.get().strip().upper(), self.selected_id),
                commit=True,
            )
            messagebox.showinfo("Success", "Course updated.")
            self.clear_form()
            self.refresh()
            if self.on_change:
                self.on_change()
        except sqlite3.IntegrityError:
            messagebox.showerror("Error", "A course with that name or code already exists.")

    def delete_course(self):
        if not self.selected_id:
            messagebox.showwarning("No selection", "Select a course in the table first.")
            return
        if not messagebox.askyesno(
            "Confirm",
            "Delete this course? This also removes every teacher assignment, timetable entries and any grades "
            "recorded for it. This cannot be undone.",
        ):
            return
        self.db.run("DELETE FROM courses WHERE id=?", (self.selected_id,), commit=True)
        self.clear_form()
        self.refresh()
        if self.on_change:
            self.on_change()

    def refresh(self):
        for row in self.tree.get_children():
            self.tree.delete(row)
        query = "SELECT id, name, code FROM courses"
        term = self.search_var.get().strip()
        params = ()
        if term:
            query += " WHERE name LIKE ? OR code LIKE ?"
            params = (f"%{term}%", f"%{term}%")
        query += " ORDER BY name"
        for row in self.db.run(query, params).fetchall():
            self.tree.insert("", "end", values=row)


# -- 5. Course Assignments tab (teacher + course -> 3+ classes) ---------
class CourseAssignmentsAdminTab(ttk.Frame):
    def __init__(self, parent, db: Database):
        super().__init__(parent)
        self.db = db
        self._teacher_map = {}
        self._course_map = {}
        self._build_ui()
        self.refresh_dropdowns()
        self.refresh()

    def _build_ui(self):
        form = ttk.LabelFrame(
            self, text=f"Assign a Teacher to a Course (select at least {MIN_CLASSES_PER_COURSE_ASSIGNMENT} classes)"
        )
        form.pack(fill="x", padx=10, pady=8)

        ttk.Label(form, text="Teacher:").grid(row=0, column=0, sticky="e", padx=4, pady=4)
        self.teacher_var = tk.StringVar()
        self.teacher_combo = ttk.Combobox(form, textvariable=self.teacher_var, width=26, state="readonly")
        self.teacher_combo.grid(row=0, column=1, padx=4, pady=4)

        ttk.Label(form, text="Course:").grid(row=0, column=2, sticky="e", padx=4, pady=4)
        self.course_var = tk.StringVar()
        self.course_combo = ttk.Combobox(form, textvariable=self.course_var, width=26, state="readonly")
        self.course_combo.grid(row=0, column=3, padx=4, pady=4)

        ttk.Label(form, text="Classes\n(ctrl/shift-click\nto multi-select):", justify="left").grid(
            row=1, column=0, sticky="ne", padx=4, pady=4
        )
        list_frame = ttk.Frame(form)
        list_frame.grid(row=1, column=1, padx=4, pady=4, sticky="w")
        self.class_listbox = tk.Listbox(list_frame, selectmode=tk.MULTIPLE, height=6, exportselection=False)
        for c in CLASSES:
            self.class_listbox.insert("end", c)
        self.class_listbox.pack(side="left")
        lb_scroll = ttk.Scrollbar(list_frame, orient="vertical", command=self.class_listbox.yview)
        self.class_listbox.configure(yscrollcommand=lb_scroll.set)
        lb_scroll.pack(side="left", fill="y")

        ttk.Button(form, text="Assign to Selected Classes", command=self.assign).grid(
            row=1, column=2, columnspan=2, padx=8, pady=4, sticky="n"
        )

        btn_frame = ttk.Frame(self)
        btn_frame.pack(fill="x", padx=10, pady=(0, 8))
        ttk.Button(btn_frame, text="Remove Selected Assignment", command=self.remove_selected).pack(side="left", padx=4)

        search_frame = ttk.Frame(self)
        search_frame.pack(fill="x", padx=10)
        ttk.Label(search_frame, text="Search:").pack(side="left")
        self.search_var = tk.StringVar()
        self.search_var.trace_add("write", lambda *a: self.refresh())
        ttk.Entry(search_frame, textvariable=self.search_var, width=30).pack(side="left", padx=6)

        table_frame = ttk.Frame(self)
        table_frame.pack(fill="both", expand=True, padx=10, pady=8)
        cols = ("id", "teacher", "course", "class")
        self.tree = ttk.Treeview(table_frame, columns=cols, show="headings", selectmode="browse")
        for c, h, w in zip(cols, ["ID", "Teacher", "Course", "Class"], [40, 170, 170, 110]):
            self.tree.heading(c, text=h)
            self.tree.column(c, width=w, anchor="center")
        vsb = ttk.Scrollbar(table_frame, orient="vertical", command=self.tree.yview)
        self.tree.configure(yscrollcommand=vsb.set)
        self.tree.pack(side="left", fill="both", expand=True)
        vsb.pack(side="right", fill="y")

    def refresh_dropdowns(self):
        rows = self.db.run("SELECT id, name FROM teachers ORDER BY name").fetchall()
        self._teacher_map = {name: tid for tid, name in rows}
        self.teacher_combo["values"] = list(self._teacher_map.keys())

        rows = self.db.run("SELECT id, name FROM courses ORDER BY name").fetchall()
        self._course_map = {name: cid for cid, name in rows}
        self.course_combo["values"] = list(self._course_map.keys())

    def assign(self):
        teacher_name = self.teacher_var.get()
        course_name = self.course_var.get()
        if not teacher_name or not course_name:
            messagebox.showerror("Validation error", "Choose both a teacher and a course.")
            return
        selected_indices = self.class_listbox.curselection()
        if len(selected_indices) < MIN_CLASSES_PER_COURSE_ASSIGNMENT:
            messagebox.showerror(
                "Validation error",
                f"Select at least {MIN_CLASSES_PER_COURSE_ASSIGNMENT} classes for this course assignment.",
            )
            return
        teacher_id = self._teacher_map[teacher_name]
        course_id = self._course_map[course_name]
        classes = [self.class_listbox.get(i) for i in selected_indices]
        added, skipped = 0, 0
        for cls in classes:
            cur = self.db.run(
                "INSERT OR IGNORE INTO course_assignments (teacher_id, course_id, class_name) VALUES (?, ?, ?)",
                (teacher_id, course_id, cls),
                commit=True,
            )
            if cur.rowcount:
                added += 1
            else:
                skipped += 1
        msg = f"{teacher_name} assigned to teach {course_name} in {added} class(es)."
        if skipped:
            msg += f" ({skipped} class(es) were already assigned.)"
        messagebox.showinfo("Assigned", msg)
        self.refresh()

    def remove_selected(self):
        sel = self.tree.selection()
        if not sel:
            messagebox.showwarning("No selection", "Select an assignment row to remove.")
            return
        values = self.tree.item(sel[0], "values")
        if not messagebox.askyesno(
            "Confirm", f"Remove {values[1]} from teaching {values[2]} in {values[3]}?\n"
                       "(Previously recorded grades are kept.)",
        ):
            return
        self.db.run("DELETE FROM course_assignments WHERE id=?", (values[0],), commit=True)
        self.refresh()

    def refresh(self):
        for row in self.tree.get_children():
            self.tree.delete(row)
        query = (
            "SELECT ca.id, t.name, c.name, ca.class_name FROM course_assignments ca "
            "JOIN teachers t ON ca.teacher_id = t.id "
            "JOIN courses c ON ca.course_id = c.id"
        )
        term = self.search_var.get().strip()
        params = ()
        if term:
            query += " WHERE t.name LIKE ? OR c.name LIKE ? OR ca.class_name LIKE ?"
            params = tuple(f"%{term}%" for _ in range(3))
        query += " ORDER BY t.name, c.name, ca.class_name"
        for row in self.db.run(query, params).fetchall():
            self.tree.insert("", "end", values=row)



# -- 6. Timetable tab (Admin compiles per-class weekly timetables) ------
class TimetableAdminTab(ttk.Frame):
    def __init__(self, parent, db):
        super().__init__(parent)
        self.db = db
        self._teacher_map = {}
        self._course_map = {}
        self._build_ui()
        self.refresh_dropdowns()
        self.load_grid()

    def _build_ui(self):
        top = ttk.Frame(self)
        top.pack(fill="x", padx=10, pady=8)
        ttk.Label(top, text="Class:").pack(side="left")
        self.class_var = tk.StringVar(value=CLASSES[0])
        class_combo = ttk.Combobox(top, textvariable=self.class_var, values=CLASSES, state="readonly", width=15)
        class_combo.pack(side="left", padx=6)
        class_combo.bind("<<ComboboxSelected>>", lambda e: self.load_grid())
        ttk.Button(top, text="Print / Export", command=self.print_timetable).pack(side="left", padx=10)

        editor = ttk.LabelFrame(self, text="Set a Timetable Cell")
        editor.pack(fill="x", padx=10, pady=8)
        ttk.Label(editor, text="Day:").grid(row=0, column=0, sticky="e", padx=4, pady=4)
        self.day_var = tk.StringVar(value=DAYS[0])
        ttk.Combobox(editor, textvariable=self.day_var, values=DAYS, state="readonly", width=12).grid(
            row=0, column=1, padx=4, pady=4
        )
        ttk.Label(editor, text="Period:").grid(row=0, column=2, sticky="e", padx=4, pady=4)
        self.period_var = tk.StringVar(value=PERIODS[0])
        ttk.Combobox(editor, textvariable=self.period_var, values=PERIODS, state="readonly", width=24).grid(
            row=0, column=3, padx=4, pady=4
        )
        ttk.Label(editor, text="Course:").grid(row=1, column=0, sticky="e", padx=4, pady=4)
        self.course_var = tk.StringVar()
        self.course_combo = ttk.Combobox(editor, textvariable=self.course_var, width=20, state="readonly")
        self.course_combo.grid(row=1, column=1, padx=4, pady=4)
        ttk.Label(editor, text="Teacher:").grid(row=1, column=2, sticky="e", padx=4, pady=4)
        self.teacher_var = tk.StringVar()
        self.teacher_combo = ttk.Combobox(editor, textvariable=self.teacher_var, width=20, state="readonly")
        self.teacher_combo.grid(row=1, column=3, padx=4, pady=4)
        btn_frame = ttk.Frame(editor)
        btn_frame.grid(row=2, column=0, columnspan=4, pady=8)
        ttk.Button(btn_frame, text="Set Cell", command=self.set_cell).pack(side="left", padx=4)
        ttk.Button(btn_frame, text="Clear Cell", command=self.clear_cell).pack(side="left", padx=4)

        grid_frame = ttk.LabelFrame(self, text="Timetable Preview")
        grid_frame.pack(fill="both", expand=True, padx=10, pady=8)
        cols = ["period"] + [d.lower() for d in DAYS]
        self.tree = ttk.Treeview(grid_frame, columns=cols, show="headings", selectmode="browse", height=len(PERIODS))
        self.tree.heading("period", text="Period")
        self.tree.column("period", width=170, anchor="w")
        for d, col in zip(DAYS, cols[1:]):
            self.tree.heading(col, text=d)
            self.tree.column(col, width=110, anchor="center")
        self.tree.pack(fill="both", expand=True, padx=6, pady=6)

    def refresh_dropdowns(self):
        rows = self.db.run("SELECT id, name FROM courses ORDER BY name").fetchall()
        self._course_map = {name: cid for cid, name in rows}
        self.course_combo["values"] = [""] + list(self._course_map.keys())
        rows = self.db.run("SELECT id, name FROM teachers ORDER BY name").fetchall()
        self._teacher_map = {name: tid for tid, name in rows}
        self.teacher_combo["values"] = [""] + list(self._teacher_map.keys())

    def load_grid(self):
        for row in self.tree.get_children():
            self.tree.delete(row)
        grid = get_timetable_grid(self.db, self.class_var.get())
        for period in PERIODS:
            row_vals = [period]
            for day in DAYS:
                course_name, teacher_name = grid.get((day, period), (None, None))
                row_vals.append(format_timetable_cell(course_name, teacher_name))
            self.tree.insert("", "end", values=row_vals)

    def set_cell(self):
        cls, day, period = self.class_var.get(), self.day_var.get(), self.period_var.get()
        course_id = self._course_map.get(self.course_var.get())
        teacher_id = self._teacher_map.get(self.teacher_var.get())
        if not course_id and not teacher_id:
            messagebox.showerror("Validation error", "Choose at least a course or a teacher for this slot.")
            return
        self.db.run(
            "INSERT INTO timetable_entries (class_name, day, period, course_id, teacher_id) VALUES (?,?,?,?,?) "
            "ON CONFLICT(class_name, day, period) DO UPDATE SET "
            "course_id=excluded.course_id, teacher_id=excluded.teacher_id",
            (cls, day, period, course_id, teacher_id),
            commit=True,
        )
        self.load_grid()

    def clear_cell(self):
        self.db.run(
            "DELETE FROM timetable_entries WHERE class_name=? AND day=? AND period=?",
            (self.class_var.get(), self.day_var.get(), self.period_var.get()),
            commit=True,
        )
        self.load_grid()

    def print_timetable(self):
        open_timetable_window(self, self.db, self.class_var.get())


# -- 8. Fees tab: fees are set PER CLASS; payments are recorded per student
class FeesAdminTab(ttk.Frame):
    def __init__(self, parent, db):
        super().__init__(parent)
        self.db = db
        self._all_students = {}          # "Name (Class)" -> id
        self._build_ui()
        self.refresh_all()

    # -- layout ---------------------------------------------------------
    def _build_ui(self):
        cf = ttk.LabelFrame(self, text="Set Fees by Class  (every student in the class is billed this amount for the term)")
        cf.pack(fill="x", padx=10, pady=(8, 4))
        ttk.Label(cf, text="Class:").grid(row=0, column=0, sticky="e", padx=4, pady=4)
        self.fee_class_var = tk.StringVar(value=CLASSES[0])
        ttk.Combobox(cf, textvariable=self.fee_class_var, values=CLASSES, state="readonly", width=12).grid(
            row=0, column=1, padx=4, pady=4
        )
        ttk.Label(cf, text="Term:").grid(row=0, column=2, sticky="e", padx=4, pady=4)
        self.fee_term_var = tk.StringVar(value=TERMS[0])
        ttk.Combobox(cf, textvariable=self.fee_term_var, values=TERMS, state="readonly", width=13).grid(
            row=0, column=3, padx=4, pady=4
        )
        ttk.Label(cf, text="Fee per student:").grid(row=0, column=4, sticky="e", padx=4, pady=4)
        self.fee_amount_var = tk.StringVar()
        ttk.Entry(cf, textvariable=self.fee_amount_var, width=12).grid(row=0, column=5, padx=4, pady=4)
        ttk.Button(cf, text="Set Class Fee", command=self.set_class_fee).grid(row=0, column=6, padx=6, pady=4)
        ttk.Button(cf, text="Remove Selected", command=self.remove_class_fee).grid(row=0, column=7, padx=2, pady=4)

        cols = ("class", "term", "amount", "students")
        self.class_fee_tree = ttk.Treeview(cf, columns=cols, show="headings", selectmode="browse", height=4)
        for c, h, w in zip(cols, ["Class", "Term", "Fee per student", "Students billed"], [110, 110, 120, 110]):
            self.class_fee_tree.heading(c, text=h)
            self.class_fee_tree.column(c, width=w, anchor="center")
        self.class_fee_tree.grid(row=1, column=0, columnspan=8, sticky="ew", padx=4, pady=(2, 6))
        self.class_fee_tree.bind("<<TreeviewSelect>>", self.on_class_fee_select)

        body = ttk.Frame(self)
        body.pack(fill="both", expand=True, padx=10, pady=4)

        left = ttk.LabelFrame(body, text="Record a Payment")
        left.pack(side="left", fill="both", expand=True, padx=(0, 6))
        ttk.Label(left, text="Search student:").grid(row=0, column=0, sticky="e", padx=4, pady=3)
        self.search_var = tk.StringVar()
        self.search_var.trace_add("write", lambda *a: self._on_search())
        ttk.Entry(left, textvariable=self.search_var, width=26).grid(row=0, column=1, columnspan=2, sticky="w", padx=4, pady=3)
        ttk.Label(left, text="(name or class)", foreground="#666666").grid(row=0, column=3, sticky="w")

        ttk.Label(left, text="Student:").grid(row=1, column=0, sticky="e", padx=4, pady=3)
        self.student_var = tk.StringVar()
        self.student_combo = ttk.Combobox(left, textvariable=self.student_var, width=28, state="readonly")
        self.student_combo.grid(row=1, column=1, columnspan=2, sticky="w", padx=4, pady=3)
        self.student_combo.bind("<<ComboboxSelected>>", lambda e: self.refresh_summary())
        ttk.Label(left, text="Term:").grid(row=1, column=3, sticky="e", padx=4, pady=3)
        self.term_var = tk.StringVar(value=TERMS[0])
        term_combo = ttk.Combobox(left, textvariable=self.term_var, values=TERMS, state="readonly", width=12)
        term_combo.grid(row=1, column=4, padx=4, pady=3)
        term_combo.bind("<<ComboboxSelected>>", lambda e: self.refresh_summary())

        self.summary_var = tk.StringVar(value="Amount Due: -    Amount Paid: -    Balance: -")
        ttk.Label(left, textvariable=self.summary_var, font=("Segoe UI", 10, "bold")).grid(
            row=2, column=0, columnspan=5, sticky="w", padx=4, pady=(4, 6)
        )

        ttk.Label(left, text="Amount Paid:").grid(row=3, column=0, sticky="e", padx=4, pady=3)
        self.amount_paid_var = tk.StringVar()
        ttk.Entry(left, textvariable=self.amount_paid_var, width=12).grid(row=3, column=1, sticky="w", padx=4, pady=3)
        ttk.Label(left, text="Date:").grid(row=3, column=2, sticky="e", padx=4, pady=3)
        self.payment_date_var = tk.StringVar(value=datetime.now().strftime("%Y-%m-%d"))
        ttk.Entry(left, textvariable=self.payment_date_var, width=12).grid(row=3, column=3, columnspan=2, sticky="w", padx=4, pady=3)
        ttk.Label(left, text="Method:").grid(row=4, column=0, sticky="e", padx=4, pady=3)
        self.method_var = tk.StringVar(value=PAYMENT_METHODS[0])
        ttk.Combobox(left, textvariable=self.method_var, values=PAYMENT_METHODS, state="readonly", width=12).grid(
            row=4, column=1, sticky="w", padx=4, pady=3
        )
        ttk.Label(left, text="Note:").grid(row=4, column=2, sticky="e", padx=4, pady=3)
        self.note_var = tk.StringVar()
        ttk.Entry(left, textvariable=self.note_var, width=18).grid(row=4, column=3, columnspan=2, sticky="w", padx=4, pady=3)
        ttk.Button(left, text="Record Payment", command=self.record_payment).grid(
            row=5, column=0, columnspan=5, pady=6
        )

        cols2 = ("id", "date", "amount", "method", "note")
        self.history_tree = ttk.Treeview(left, columns=cols2, show="headings", selectmode="browse", height=5)
        for c, h, w in zip(cols2, ["ID", "Date", "Amount", "Method", "Note"], [35, 85, 70, 90, 120]):
            self.history_tree.heading(c, text=h)
            self.history_tree.column(c, width=w, anchor="center")
        self.history_tree.grid(row=6, column=0, columnspan=5, sticky="nsew", padx=4, pady=2)
        ttk.Button(left, text="Delete Selected Payment", command=self.delete_payment).grid(
            row=7, column=0, columnspan=5, sticky="w", padx=4, pady=(2, 6)
        )
        left.rowconfigure(6, weight=1)

        right = ttk.LabelFrame(body, text="School Fees Overview")
        right.pack(side="left", fill="both", expand=True, padx=(6, 0))
        top2 = ttk.Frame(right)
        top2.pack(fill="x", padx=6, pady=4)
        ttk.Label(top2, text="Term:").pack(side="left")
        self.overview_term_var = tk.StringVar(value=TERMS[0])
        ov_term = ttk.Combobox(top2, textvariable=self.overview_term_var, values=TERMS, state="readonly", width=12)
        ov_term.pack(side="left", padx=4)
        ov_term.bind("<<ComboboxSelected>>", lambda e: self.refresh_overview())
        ttk.Label(top2, text="Class:").pack(side="left", padx=(8, 0))
        self.overview_class_var = tk.StringVar(value="All classes")
        ov_class = ttk.Combobox(top2, textvariable=self.overview_class_var, values=["All classes"] + CLASSES,
                                state="readonly", width=11)
        ov_class.pack(side="left", padx=4)
        ov_class.bind("<<ComboboxSelected>>", lambda e: self.refresh_overview())
        cols3 = ("student", "class", "due", "paid", "balance")
        self.overview_tree = ttk.Treeview(right, columns=cols3, show="headings", selectmode="browse")
        for c, h, w in zip(cols3, ["Student", "Class", "Due", "Paid", "Balance"], [140, 70, 70, 70, 70]):
            self.overview_tree.heading(c, text=h)
            self.overview_tree.column(c, width=w, anchor="center")
        self.overview_tree.pack(fill="both", expand=True, padx=6, pady=6)
        self.overview_tree.bind("<<TreeviewSelect>>", self.on_overview_select)

    # -- refreshing --------------------------------------------------------
    def refresh_all(self):
        self.refresh_students()
        self.refresh_class_fees()
        self.refresh_overview()
        self.refresh_summary()

    def _on_search(self):
        self.refresh_students()
        self.refresh_overview()

    def _matches_search(self, name, cls):
        term = self.search_var.get().strip().lower()
        return not term or term in name.lower() or term in cls.lower()

    def refresh_students(self):
        rows = self.db.run("SELECT id, name, student_class FROM students ORDER BY name").fetchall()
        self._all_students = {f"{name} ({cls})": sid for sid, name, cls in rows}
        self.student_combo["values"] = [
            f"{name} ({cls})" for _sid, name, cls in rows if self._matches_search(name, cls)
        ]

    def refresh_class_fees(self):
        for r in self.class_fee_tree.get_children():
            self.class_fee_tree.delete(r)
        rows = self.db.run("SELECT class_name, term, amount_due FROM class_fees").fetchall()
        rows.sort(key=lambda r: (CLASSES.index(r[0]) if r[0] in CLASSES else 99,
                                 TERMS.index(r[1]) if r[1] in TERMS else 99))
        for cls, term, amount in rows:
            count = self.db.run("SELECT COUNT(*) FROM students WHERE student_class=?", (cls,)).fetchone()[0]
            self.class_fee_tree.insert("", "end", values=(cls, term, f"{amount:.2f}", count))

    def refresh_summary(self):
        sid = self._all_students.get(self.student_var.get())
        for r in self.history_tree.get_children():
            self.history_tree.delete(r)
        if not sid:
            return
        due, paid, balance = compute_fee_balance(self.db, sid, self.term_var.get())
        self.summary_var.set(f"Amount Due: {due:.2f}    Amount Paid: {paid:.2f}    Balance: {balance:.2f}")
        rows = self.db.run(
            "SELECT id, payment_date, amount_paid, method, COALESCE(note,'') FROM fee_payments "
            "WHERE student_id=? AND term=? ORDER BY payment_date DESC",
            (sid, self.term_var.get()),
        ).fetchall()
        for row in rows:
            self.history_tree.insert("", "end", values=row)

    def refresh_overview(self):
        for r in self.overview_tree.get_children():
            self.overview_tree.delete(r)
        term = self.overview_term_var.get()
        cls_filter = self.overview_class_var.get()
        rows = self.db.run("SELECT id, name, student_class FROM students ORDER BY student_class, name").fetchall()
        for sid, name, cls in rows:
            if cls_filter != "All classes" and cls != cls_filter:
                continue
            if not self._matches_search(name, cls):
                continue
            due, paid, balance = compute_fee_balance(self.db, sid, term)
            self.overview_tree.insert("", "end", values=(name, cls, f"{due:.2f}", f"{paid:.2f}", f"{balance:.2f}"))

    # -- class fees ----------------------------------------------------------
    def on_class_fee_select(self, _event=None):
        sel = self.class_fee_tree.selection()
        if not sel:
            return
        cls, term, amount, _count = self.class_fee_tree.item(sel[0], "values")
        self.fee_class_var.set(cls)
        self.fee_term_var.set(term)
        self.fee_amount_var.set(amount)

    def set_class_fee(self):
        cls, term = self.fee_class_var.get(), self.fee_term_var.get()
        try:
            amount = float(self.fee_amount_var.get())
            if amount < 0:
                raise ValueError
        except ValueError:
            messagebox.showerror("Validation error", "Fee per student must be a non-negative number.")
            return
        self.db.run(
            "INSERT INTO class_fees (class_name, term, amount_due, created_at) VALUES (?, ?, ?, ?) "
            "ON CONFLICT(class_name, term) DO UPDATE SET amount_due=excluded.amount_due",
            (cls, term, amount, datetime.now().isoformat()),
            commit=True,
        )
        count = self.db.run("SELECT COUNT(*) FROM students WHERE student_class=?", (cls,)).fetchone()[0]
        messagebox.showinfo("Saved", f"{cls} fee for {term} set to {amount:.2f} per student ({count} student(s) billed).")
        self.fee_amount_var.set("")
        self.refresh_all()

    def remove_class_fee(self):
        sel = self.class_fee_tree.selection()
        if not sel:
            messagebox.showwarning("No selection", "Select a class fee in the table first.")
            return
        cls, term, _amount, _count = self.class_fee_tree.item(sel[0], "values")
        if not messagebox.askyesno("Confirm", f"Remove the {term} fee for {cls}? Payments already recorded are kept."):
            return
        self.db.run("DELETE FROM class_fees WHERE class_name=? AND term=?", (cls, term), commit=True)
        self.refresh_all()

    # -- payments ---------------------------------------------------------------
    def on_overview_select(self, _event=None):
        sel = self.overview_tree.selection()
        if not sel:
            return
        name, cls = self.overview_tree.item(sel[0], "values")[:2]
        label = f"{name} ({cls})"
        if label in self._all_students:
            self.student_var.set(label)
            self.term_var.set(self.overview_term_var.get())
            self.refresh_summary()

    def record_payment(self):
        sid = self._all_students.get(self.student_var.get())
        if not sid:
            messagebox.showerror("Validation error", "Choose a student first (use the search box to find one).")
            return
        try:
            amount = float(self.amount_paid_var.get())
            if amount <= 0:
                raise ValueError
        except ValueError:
            messagebox.showerror("Validation error", "Amount Paid must be a positive number.")
            return
        if not self.payment_date_var.get().strip():
            messagebox.showerror("Validation error", "Enter a payment date.")
            return
        self.db.run(
            "INSERT INTO fee_payments (student_id, term, amount_paid, payment_date, method, note, recorded_by) "
            "VALUES (?, ?, ?, ?, ?, ?, ?)",
            (sid, self.term_var.get(), amount, self.payment_date_var.get().strip(),
             self.method_var.get(), self.note_var.get().strip(), "Admin"),
            commit=True,
        )
        messagebox.showinfo("Recorded", f"Payment of {amount:.2f} recorded.")
        self.amount_paid_var.set("")
        self.note_var.set("")
        self.refresh_summary()
        self.refresh_overview()

    def delete_payment(self):
        sel = self.history_tree.selection()
        if not sel:
            messagebox.showwarning("No selection", "Select a payment row to delete.")
            return
        values = self.history_tree.item(sel[0], "values")
        if not messagebox.askyesno("Confirm", "Delete this payment record?"):
            return
        self.db.run("DELETE FROM fee_payments WHERE id=?", (values[0],), commit=True)
        self.refresh_summary()
        self.refresh_overview()


# -- 9. Attendance tab (clock-in window settings + teacher/student logs) --
class AttendanceAdminTab(ttk.Frame):
    def __init__(self, parent, db):
        super().__init__(parent)
        self.db = db
        self._build_ui()
        self.load_settings()
        self.refresh_teacher_log()

    def _build_ui(self):
        settings = ttk.LabelFrame(self, text="Teacher Clock-in Times")
        settings.pack(fill="x", padx=10, pady=8)
        ttk.Label(settings, text="Clock-in opens at (HH:MM):").grid(row=0, column=0, sticky="e", padx=6, pady=4)
        self.open_time_var = tk.StringVar()
        ttk.Entry(settings, textvariable=self.open_time_var, width=8).grid(row=0, column=1, sticky="w", padx=4)
        ttk.Label(settings, text="Reporting time (HH:MM):").grid(row=0, column=2, sticky="e", padx=6, pady=4)
        self.reporting_time_var = tk.StringVar()
        ttk.Entry(settings, textvariable=self.reporting_time_var, width=8).grid(row=0, column=3, sticky="w", padx=4)
        ttk.Button(settings, text="Save", command=self.save_settings).grid(row=0, column=4, padx=10)
        ttk.Label(
            settings,
            text=(f"Teachers can clock in only from the opening time until {CLOCK_IN_CLOSING_TIME} (4:00 pm). "
                  "Clocking in after the reporting time is marked Late; "
                  "set both times the same to open clock-in exactly at the reporting time."),
            foreground="#666666", wraplength=820, justify="left",
        ).grid(row=1, column=0, columnspan=5, sticky="w", padx=6, pady=(0, 6))

        teacher_frame = ttk.LabelFrame(self, text="Teacher Attendance Log")
        teacher_frame.pack(fill="both", expand=True, padx=10, pady=8)
        filt = ttk.Frame(teacher_frame)
        filt.pack(fill="x", padx=6, pady=4)
        ttk.Label(filt, text="Date (YYYY-MM-DD, blank = all):").pack(side="left")
        self.date_filter_var = tk.StringVar()
        ttk.Entry(filt, textvariable=self.date_filter_var, width=14).pack(side="left", padx=6)
        ttk.Button(filt, text="Refresh", command=self.refresh_teacher_log).pack(side="left", padx=6)

        cols = ("teacher", "date", "time", "status")
        self.teacher_tree = ttk.Treeview(teacher_frame, columns=cols, show="headings", selectmode="browse")
        for c, h, w in zip(cols, ["Teacher", "Date", "Clock-in Time", "Status"], [170, 100, 110, 90]):
            self.teacher_tree.heading(c, text=h)
            self.teacher_tree.column(c, width=w, anchor="center")
        self.teacher_tree.pack(fill="both", expand=True, padx=6, pady=6)

        student_frame = ttk.LabelFrame(self, text="Student Attendance Overview")
        student_frame.pack(fill="both", expand=True, padx=10, pady=8)
        top2 = ttk.Frame(student_frame)
        top2.pack(fill="x", padx=6, pady=4)
        ttk.Label(top2, text="Class:").pack(side="left")
        self.overview_class_var = tk.StringVar()
        ttk.Combobox(top2, textvariable=self.overview_class_var, values=CLASSES, state="readonly", width=15).pack(
            side="left", padx=6
        )
        ttk.Label(top2, text="Date (YYYY-MM-DD):").pack(side="left")
        self.overview_date_var = tk.StringVar(value=datetime.now().strftime("%Y-%m-%d"))
        ttk.Entry(top2, textvariable=self.overview_date_var, width=14).pack(side="left", padx=6)
        ttk.Button(top2, text="View", command=self.refresh_student_overview).pack(side="left", padx=6)

        cols2 = ("student", "status")
        self.student_tree = ttk.Treeview(student_frame, columns=cols2, show="headings", selectmode="browse")
        for c, h, w in zip(cols2, ["Student", "Status"], [200, 120]):
            self.student_tree.heading(c, text=h)
            self.student_tree.column(c, width=w, anchor="center")
        self.student_tree.pack(fill="both", expand=True, padx=6, pady=6)

    def load_settings(self):
        self.open_time_var.set(get_setting(self.db, ATTENDANCE_OPEN_KEY, DEFAULT_ATTENDANCE_OPEN_TIME))
        self.reporting_time_var.set(get_setting(self.db, REPORTING_TIME_KEY, DEFAULT_REPORTING_TIME))

    def save_settings(self):
        opens, reporting = self.open_time_var.get().strip(), self.reporting_time_var.get().strip()
        try:
            t_open = datetime.strptime(opens, "%H:%M").time()
            t_report = datetime.strptime(reporting, "%H:%M").time()
        except ValueError:
            messagebox.showerror("Validation error", "Enter both times as 24-hour HH:MM, e.g. 06:00 and 07:30.")
            return
        t_close = datetime.strptime(CLOCK_IN_CLOSING_TIME, "%H:%M").time()
        if t_open > t_report:
            messagebox.showerror("Validation error", "Clock-in must open at or before the reporting time.")
            return
        if t_report >= t_close:
            messagebox.showerror("Validation error", f"The reporting time must be before {CLOCK_IN_CLOSING_TIME}.")
            return
        set_setting(self.db, ATTENDANCE_OPEN_KEY, opens)
        set_setting(self.db, REPORTING_TIME_KEY, reporting)
        messagebox.showinfo("Saved", f"Clock-in opens {opens}, reporting time {reporting}, closes {CLOCK_IN_CLOSING_TIME}.")

    def refresh_teacher_log(self):
        for r in self.teacher_tree.get_children():
            self.teacher_tree.delete(r)
        query = (
            "SELECT t.name, ta.date, ta.clock_in_time, ta.status "
            "FROM teacher_attendance ta JOIN teachers t ON ta.teacher_id = t.id"
        )
        params = ()
        d = self.date_filter_var.get().strip()
        if d:
            query += " WHERE ta.date=?"
            params = (d,)
        query += " ORDER BY ta.date DESC, t.name"
        for row in self.db.run(query, params).fetchall():
            self.teacher_tree.insert("", "end", values=row)

    def refresh_student_overview(self):
        for r in self.student_tree.get_children():
            self.student_tree.delete(r)
        cls = self.overview_class_var.get()
        d = self.overview_date_var.get().strip()
        if not cls or not d:
            messagebox.showerror("Validation error", "Choose a class and a date.")
            return
        rows = self.db.run(
            "SELECT s.name, COALESCE(sa.status, '(not marked)') FROM students s "
            "LEFT JOIN student_attendance sa ON sa.student_id = s.id AND sa.date=? "
            "WHERE s.student_class=? ORDER BY s.name",
            (d, cls),
        ).fetchall()
        for row in rows:
            self.student_tree.insert("", "end", values=row)


# -- Network Sync settings (opened from the login screen) -----------------
class SyncDialog(tk.Toplevel):
    """Window holding the sync settings. Opened from the login screen so any
    user can connect this device to the network without an Admin login."""

    def __init__(self, parent, sync):
        super().__init__(parent)
        self.title("Network Sync")
        self.geometry("820x600")
        self.minsize(700, 520)
        SyncAdminTab(self, sync).pack(fill="both", expand=True)
        ttk.Button(self, text="Close", command=self.destroy).pack(anchor="e", padx=12, pady=(0, 10))


class SyncAdminTab(ttk.Frame):
    def __init__(self, parent, sync):
        super().__init__(parent)
        self.sync = sync
        self._build_ui()
        self.load()
        self._tick()

    def _build_ui(self):
        box = ttk.LabelFrame(self, text="Sync server connection")
        box.pack(fill="x", padx=10, pady=8)
        ttk.Label(box, text="Server address:").grid(row=0, column=0, sticky="e", padx=6, pady=5)
        self.url_var = tk.StringVar()
        ttk.Entry(box, textvariable=self.url_var, width=48).grid(row=0, column=1, sticky="w", padx=4, pady=5)
        ttk.Label(box, text="e.g. https://sync.myschool.example:8765", foreground="#666666").grid(
            row=0, column=2, sticky="w", padx=6
        )
        ttk.Label(box, text="API key:").grid(row=1, column=0, sticky="e", padx=6, pady=5)
        self.key_var = tk.StringVar()
        make_password_entry(box, self.key_var, 40).grid(row=1, column=1, sticky="w", padx=4, pady=5)
        self.enabled_var = tk.BooleanVar(value=False)
        ttk.Checkbutton(box, text="Enable automatic sync", variable=self.enabled_var).grid(
            row=2, column=1, sticky="w", padx=4, pady=3
        )
        ttk.Label(box, text="Check for changes every (seconds):").grid(row=3, column=0, sticky="e", padx=6, pady=3)
        self.interval_var = tk.StringVar(value="30")
        ttk.Entry(box, textvariable=self.interval_var, width=8).grid(row=3, column=1, sticky="w", padx=4, pady=3)

        buttons = ttk.Frame(box)
        buttons.grid(row=4, column=0, columnspan=3, sticky="w", padx=6, pady=8)
        ttk.Button(buttons, text="Save settings", command=self.save).pack(side="left", padx=3)
        ttk.Button(buttons, text="Test connection", command=self.test).pack(side="left", padx=3)
        ttk.Button(buttons, text="Sync now", command=self.sync_now).pack(side="left", padx=3)
        ttk.Button(buttons, text="Full re-sync", command=self.full_resync).pack(side="left", padx=3)

        status = ttk.LabelFrame(self, text="Status")
        status.pack(fill="both", expand=True, padx=10, pady=8)
        self.status_var = tk.StringVar()
        ttk.Label(status, textvariable=self.status_var, font=("Segoe UI", 10, "bold")).pack(anchor="w", padx=8, pady=(6, 2))
        self.detail_var = tk.StringVar()
        ttk.Label(status, textvariable=self.detail_var, foreground="#555555").pack(anchor="w", padx=8)
        self.log = tk.Text(status, height=9, state="disabled", wrap="word")
        self.log.pack(fill="both", expand=True, padx=8, pady=8)
        ttk.Label(
            status,
            text=("Every change made on any device is pushed to the sync server and pulled onto the others, "
                  "over your internet connection. While offline, changes are kept and sent when the connection "
                  "returns. Start the server with school_sync_server.py and use the same API key on every device."),
            foreground="#666666", wraplength=820, justify="left",
        ).pack(anchor="w", padx=8, pady=(0, 8))

    def load(self):
        cfg = self.sync.get_config()
        self.url_var.set(cfg["url"])
        self.key_var.set(cfg["api_key"])
        self.enabled_var.set(cfg["enabled"])
        self.interval_var.set(str(cfg["interval"]))

    def save(self):
        try:
            self.sync.save_config(self.url_var.get(), self.key_var.get(), self.enabled_var.get(), self.interval_var.get())
        except ValueError as exc:
            messagebox.showerror("Invalid settings", str(exc))
            return False
        messagebox.showinfo("Saved", "Sync settings saved.")
        return True

    def test(self):
        ok, message = self.sync.test_connection(self.url_var.get(), self.key_var.get())
        (messagebox.showinfo if ok else messagebox.showerror)("Connection test", message)

    def sync_now(self):
        if not self.save():
            return
        if not self.sync.sync_now():
            messagebox.showinfo("Sync", "A sync is already running, or sync is not set up yet.")

    def full_resync(self):
        if not messagebox.askyesno(
            "Full re-sync",
            "Re-send everything from this device and re-download everything from the server?\n"
            "Use this if devices seem out of step. It is safe but can take a while.",
        ):
            return
        if not self.save():
            return
        self.sync.force_full_resync()
        self.sync.sync_now()

    def _tick(self):
        try:
            self.status_var.set(self.sync.status_summary())
            cfg = self.sync.get_config()
            when = cfg["last_sync_at"].replace("T", " ") if cfg["last_sync_at"] else "never"
            self.detail_var.set(f"Waiting to upload: {self.sync.pending_count()}   |   Last successful sync: {when}")
            self.log.config(state="normal")
            self.log.delete("1.0", "end")
            self.log.insert("1.0", "\n".join(reversed(self.sync.log_lines)))
            self.log.config(state="disabled")
            self.after(2000, self._tick)
        except tk.TclError:
            pass                     # tab was destroyed (logout): stop updating


# ----------------------------------------------------------------------
# Teacher dashboard
# ----------------------------------------------------------------------
class TeacherDashboard(ttk.Frame):
    def __init__(self, parent, controller):
        super().__init__(parent)
        self.controller = controller
        self.db = controller.db
        self.teacher = controller.current_user

        TopBar(self, controller, "Teacher Dashboard").pack(fill="x")

        status = (
            f"Class Teacher of: {self.teacher['assigned_class']}" if self.teacher.get("assigned_class")
            else "You are not currently assigned as a Class Teacher."
        )
        ttk.Label(self, text=status, font=("Segoe UI", 10, "italic")).pack(anchor="w", padx=14, pady=(0, 6))

        notebook = ttk.Notebook(self)
        notebook.pack(fill="both", expand=True, padx=10, pady=8)

        self.my_courses_tab = MyCoursesTab(notebook, self.db, self.teacher)
        self.class_overview_tab = ClassOverviewTab(notebook, self.db, self.teacher)
        self.results_tab = ResultsSlipTab(notebook, self.db, self.teacher)
        self.timetable_tab = TeacherTimetableTab(notebook, self.db, self.teacher)
        # Announcements: only a Class Teacher may send them, and only to their own class.
        if self.teacher.get("assigned_class"):
            self.announcements_tab = AnnouncementsTab(
                notebook, self.db, "Teacher", self.teacher["name"],
                allowed_classes=[self.teacher["assigned_class"]],
            )
        else:
            self.announcements_tab = LockedTab(
                notebook,
                "Only the Admin and teachers assigned to a class (Class Teachers) can send announcements "
                "to parents.\n\nYou are not currently assigned to a class. Ask the Admin to assign you "
                "as a Class Teacher if this should change.",
            )
        self.my_attendance_tab = TeacherAttendanceTab(notebook, self.db, self.teacher)
        self.student_attendance_tab = StudentAttendanceTab(notebook, self.db, self.teacher)

        notebook.add(self.my_courses_tab, text="My Courses & Grading")
        notebook.add(self.class_overview_tab, text="Class Grade Overview")
        notebook.add(self.results_tab, text="Compile & Send Results")
        notebook.add(self.timetable_tab, text="Class Timetable")
        notebook.add(self.announcements_tab, text="Send Announcement")
        notebook.add(self.my_attendance_tab, text="My Attendance")
        notebook.add(self.student_attendance_tab, text="Student Attendance")

        notebook.bind("<<NotebookTabChanged>>", self._on_tab_changed)

    def _on_tab_changed(self, _event=None):
        self.my_courses_tab.refresh_assignments()
        self.class_overview_tab.refresh_class_list()
        self.results_tab.refresh_students()
        self.announcements_tab.refresh_students()
        self.announcements_tab.refresh_history()
        self.my_attendance_tab.refresh()

    def refresh_all(self):
        """Called after a network sync brought in changes from other devices."""
        self._on_tab_changed()


class MyCoursesTab(ttk.Frame):
    """Every (course, class) combination this teacher was assigned to teach.
    Grades are entered as a Class Score (/60 -> /50) and an Exam Score
    (/100 -> /50); their sum is the total that gets graded. Selecting a
    student/term that already has a grade loads it for editing, and a
    'Recorded Grades' list lets the teacher jump to or delete any entry."""

    def __init__(self, parent, db, teacher):
        super().__init__(parent)
        self.db = db
        self.teacher = teacher
        self.selected_assignment = None
        self.selected_student_id = None
        self._assignment_lookup = {}
        self._recorded_lookup = {}
        self._build_ui()
        self.refresh_assignments()

    def _build_ui(self):
        main = ttk.Frame(self)
        main.pack(fill="both", expand=True, padx=8, pady=8)

        left = ttk.LabelFrame(main, text="My Course Assignments")
        left.pack(side="left", fill="both", expand=True, padx=(0, 8))
        cols = ("course", "class")
        self.assign_tree = ttk.Treeview(left, columns=cols, show="headings", selectmode="browse", height=8)
        for c, h, w in zip(cols, ["Course", "Class"], [140, 100]):
            self.assign_tree.heading(c, text=h)
            self.assign_tree.column(c, width=w, anchor="center")
        self.assign_tree.pack(fill="both", expand=True, padx=6, pady=6)
        self.assign_tree.bind("<<TreeviewSelect>>", self.on_assignment_select)

        ttk.Label(left, text="Students in Class:", font=("Segoe UI", 9, "bold")).pack(anchor="w", padx=6)
        cols2 = ("id", "name")
        self.student_tree = ttk.Treeview(left, columns=cols2, show="headings", selectmode="browse", height=6)
        for c, h, w in zip(cols2, ["ID", "Name"], [40, 160]):
            self.student_tree.heading(c, text=h)
            self.student_tree.column(c, width=w, anchor="center")
        self.student_tree.pack(fill="both", expand=True, padx=6, pady=(0, 6))
        self.student_tree.bind("<<TreeviewSelect>>", self.on_student_select)

        right = ttk.Frame(main)
        right.pack(side="left", fill="both", expand=True)

        grade_form = ttk.LabelFrame(right, text="Enter / Edit Grade")
        grade_form.pack(fill="x", pady=(0, 8))
        ttk.Label(grade_form, text="Course:").grid(row=0, column=0, sticky="e", padx=4, pady=3)
        self.course_lbl_var = tk.StringVar(value="(select an assignment)")
        ttk.Label(grade_form, textvariable=self.course_lbl_var, font=("Segoe UI", 9, "bold")).grid(
            row=0, column=1, columnspan=3, sticky="w", padx=4, pady=3
        )
        ttk.Label(grade_form, text="Student:").grid(row=1, column=0, sticky="e", padx=4, pady=3)
        self.student_lbl_var = tk.StringVar(value="(select a student)")
        ttk.Label(grade_form, textvariable=self.student_lbl_var, font=("Segoe UI", 9, "bold")).grid(
            row=1, column=1, columnspan=3, sticky="w", padx=4, pady=3
        )
        ttk.Label(grade_form, text="Term:").grid(row=2, column=0, sticky="e", padx=4, pady=3)
        self.term_var = tk.StringVar(value=TERMS[0])
        term_combo = ttk.Combobox(grade_form, textvariable=self.term_var, values=TERMS, state="readonly", width=14)
        term_combo.grid(row=2, column=1, sticky="w", padx=4, pady=3)
        term_combo.bind("<<ComboboxSelected>>", lambda e: self._load_existing_grade())

        ttk.Label(grade_form, text="Class Score (out of 60):").grid(row=3, column=0, sticky="e", padx=4, pady=3)
        self.class_score_var = tk.StringVar()
        ttk.Entry(grade_form, textvariable=self.class_score_var, width=10).grid(row=3, column=1, sticky="w", padx=4, pady=3)
        ttk.Label(grade_form, text="Exam Score (out of 100):").grid(row=3, column=2, sticky="e", padx=4, pady=3)
        self.exam_score_var = tk.StringVar()
        ttk.Entry(grade_form, textvariable=self.exam_score_var, width=10).grid(row=3, column=3, sticky="w", padx=4, pady=3)
        self.class_score_var.trace_add("write", lambda *a: self._update_preview())
        self.exam_score_var.trace_add("write", lambda *a: self._update_preview())

        self.preview_var = tk.StringVar(value="Class: -/50   Exam: -/50   Total: -/100   Grade: -")
        ttk.Label(grade_form, textvariable=self.preview_var, foreground="#005599").grid(
            row=4, column=0, columnspan=4, sticky="w", padx=4, pady=(4, 6)
        )
        btns = ttk.Frame(grade_form)
        btns.grid(row=5, column=0, columnspan=4, pady=6)
        ttk.Button(btns, text="Save Grade", command=self.save_grade).pack(side="left", padx=4)
        ttk.Button(btns, text="Delete Grade", command=self.delete_grade).pack(side="left", padx=4)
        ttk.Button(btns, text="Clear Form", command=self.clear_grade_form).pack(side="left", padx=4)

        recorded_frame = ttk.LabelFrame(right, text="Recorded Grades for this Course & Class (click one to edit it)")
        recorded_frame.pack(fill="both", expand=True)
        cols3 = ("student", "term", "class_score", "exam_score", "total", "grade")
        self.recorded_tree = ttk.Treeview(recorded_frame, columns=cols3, show="headings", selectmode="browse")
        for c, h, w in zip(cols3, ["Student", "Term", "Class/50", "Exam/50", "Total", "Grade"],
                           [130, 100, 70, 70, 60, 60]):
            self.recorded_tree.heading(c, text=h)
            self.recorded_tree.column(c, width=w, anchor="center")
        self.recorded_tree.pack(fill="both", expand=True, padx=6, pady=6)
        self.recorded_tree.bind("<<TreeviewSelect>>", self.on_recorded_select)

    def refresh_assignments(self):
        for row in self.assign_tree.get_children():
            self.assign_tree.delete(row)
        rows = self.db.run(
            "SELECT ca.id, c.id, c.name, ca.class_name FROM course_assignments ca "
            "JOIN courses c ON ca.course_id = c.id WHERE ca.teacher_id=? ORDER BY c.name, ca.class_name",
            (self.teacher["id"],),
        ).fetchall()
        self._assignment_lookup = {}
        for assignment_id, course_id, course_name, class_name in rows:
            iid = str(assignment_id)
            self.assign_tree.insert("", "end", iid=iid, values=(course_name, class_name))
            self._assignment_lookup[iid] = (course_id, course_name, class_name)
        if not rows:
            self.course_lbl_var.set("(no course assignments yet - ask the Admin)")

    def on_assignment_select(self, _event=None):
        sel = self.assign_tree.selection()
        if not sel:
            return
        course_id, course_name, class_name = self._assignment_lookup[sel[0]]
        self.selected_assignment = (course_id, course_name, class_name)
        self.course_lbl_var.set(f"{course_name}  ({class_name})")
        self._refresh_students(class_name)
        self._refresh_recorded_grades()

    def _refresh_students(self, class_name):
        for row in self.student_tree.get_children():
            self.student_tree.delete(row)
        rows = self.db.run(
            "SELECT id, name FROM students WHERE student_class=? ORDER BY name", (class_name,)
        ).fetchall()
        for row in rows:
            self.student_tree.insert("", "end", values=row)
        self.clear_grade_form(keep_assignment=True)

    def _refresh_recorded_grades(self):
        for row in self.recorded_tree.get_children():
            self.recorded_tree.delete(row)
        self._recorded_lookup = {}
        if not self.selected_assignment:
            return
        course_id, _course_name, class_name = self.selected_assignment
        rows = self.db.run(
            "SELECT s.name, g.term, g.class_score_converted, g.exam_score_converted, g.score, g.grade, "
            "g.student_id, g.class_score, g.exam_score "
            "FROM grades g JOIN students s ON g.student_id = s.id "
            "WHERE g.course_id=? AND s.student_class=? ORDER BY s.name, g.term",
            (course_id, class_name),
        ).fetchall()
        for i, (name, term, class_conv, exam_conv, total, grade, student_id, class_raw, exam_raw) in enumerate(rows):
            iid = f"r{i}"
            class_str = f"{class_conv:.1f}" if class_conv is not None else "-"
            exam_str = f"{exam_conv:.1f}" if exam_conv is not None else "-"
            self.recorded_tree.insert("", "end", iid=iid, values=(name, term, class_str, exam_str, f"{total:.1f}", grade))
            self._recorded_lookup[iid] = {
                "student_id": student_id, "name": name, "term": term,
                "class_score": class_raw, "exam_score": exam_raw,
            }

    def on_student_select(self, _event=None):
        sel = self.student_tree.selection()
        if not sel:
            return
        values = self.student_tree.item(sel[0], "values")
        self.selected_student_id = values[0]
        self.student_lbl_var.set(values[1])
        self._load_existing_grade()

    def on_recorded_select(self, _event=None):
        sel = self.recorded_tree.selection()
        if not sel:
            return
        info = self._recorded_lookup.get(sel[0])
        if not info:
            return
        self.selected_student_id = info["student_id"]
        self.student_lbl_var.set(info["name"])
        self.term_var.set(info["term"])
        self.class_score_var.set("" if info["class_score"] is None else str(info["class_score"]))
        self.exam_score_var.set("" if info["exam_score"] is None else str(info["exam_score"]))

    def _load_existing_grade(self):
        """When a student + term is chosen, pre-fill any existing grade so it can be edited."""
        if not self.selected_assignment or not self.selected_student_id:
            return
        course_id = self.selected_assignment[0]
        row = self.db.run(
            "SELECT class_score, exam_score FROM grades WHERE student_id=? AND course_id=? AND term=?",
            (self.selected_student_id, course_id, self.term_var.get()),
        ).fetchone()
        self.class_score_var.set("" if not row or row[0] is None else str(row[0]))
        self.exam_score_var.set("" if not row or row[1] is None else str(row[1]))

    def _update_preview(self):
        try:
            class_conv = convert_class_score(float(self.class_score_var.get()))
            class_str = f"{class_conv:.1f}/50"
        except ValueError:
            class_conv, class_str = None, "-/50"
        try:
            exam_conv = convert_exam_score(float(self.exam_score_var.get()))
            exam_str = f"{exam_conv:.1f}/50"
        except ValueError:
            exam_conv, exam_str = None, "-/50"
        if class_conv is not None and exam_conv is not None:
            total = class_conv + exam_conv
            self.preview_var.set(
                f"Class: {class_str}   Exam: {exam_str}   Total: {total:.1f}/100   Grade: {compute_grade(total)[0]}"
            )
        else:
            self.preview_var.set(f"Class: {class_str}   Exam: {exam_str}   Total: -/100   Grade: -")

    def clear_grade_form(self, keep_assignment=False):
        self.selected_student_id = None
        self.student_lbl_var.set("(select a student)")
        self.class_score_var.set("")
        self.exam_score_var.set("")
        if self.student_tree.selection():
            self.student_tree.selection_remove(self.student_tree.selection())
        if self.recorded_tree.selection():
            self.recorded_tree.selection_remove(self.recorded_tree.selection())
        if not keep_assignment:
            self.selected_assignment = None
            self.course_lbl_var.set("(select an assignment)")

    def save_grade(self):
        if not self.selected_assignment:
            messagebox.showwarning("No selection", "Select a course assignment first.")
            return
        if not self.selected_student_id:
            messagebox.showwarning("No selection", "Select a student first.")
            return
        try:
            class_raw = float(self.class_score_var.get())
            if not (0 <= class_raw <= 60):
                raise ValueError
        except ValueError:
            messagebox.showerror("Validation error", "Class Score must be a number between 0 and 60.")
            return
        try:
            exam_raw = float(self.exam_score_var.get())
            if not (0 <= exam_raw <= 100):
                raise ValueError
        except ValueError:
            messagebox.showerror("Validation error", "Exam Score must be a number between 0 and 100.")
            return

        class_conv = convert_class_score(class_raw)
        exam_conv = convert_exam_score(exam_raw)
        total = class_conv + exam_conv
        grade, remark = compute_grade(total)
        course_id, course_name, _class_name = self.selected_assignment

        self.db.run(
            """
            INSERT INTO grades (student_id, teacher_id, course_id, subject, term,
                                 class_score, exam_score, class_score_converted, exam_score_converted,
                                 score, grade, remark)
            VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
            ON CONFLICT(student_id, course_id, term)
            DO UPDATE SET class_score=excluded.class_score, exam_score=excluded.exam_score,
                          class_score_converted=excluded.class_score_converted,
                          exam_score_converted=excluded.exam_score_converted,
                          score=excluded.score, grade=excluded.grade, remark=excluded.remark,
                          teacher_id=excluded.teacher_id, subject=excluded.subject
            """,
            (self.selected_student_id, self.teacher["id"], course_id, course_name, self.term_var.get(),
             class_raw, exam_raw, class_conv, exam_conv, total, grade, remark),
            commit=True,
        )
        messagebox.showinfo("Saved", f"Grade saved: Total {total:.1f}/100 ({grade} - {remark}).")
        self._refresh_recorded_grades()

    def delete_grade(self):
        if not self.selected_assignment or not self.selected_student_id:
            messagebox.showwarning("No selection", "Select a recorded grade (or a graded student) first.")
            return
        course_id = self.selected_assignment[0]
        existing = self.db.run(
            "SELECT id FROM grades WHERE student_id=? AND course_id=? AND term=?",
            (self.selected_student_id, course_id, self.term_var.get()),
        ).fetchone()
        if not existing:
            messagebox.showinfo("Nothing to delete", "No saved grade exists for this student/term yet.")
            return
        if not messagebox.askyesno("Confirm", "Delete this grade entry?"):
            return
        self.db.run("DELETE FROM grades WHERE id=?", (existing[0],), commit=True)
        self.class_score_var.set("")
        self.exam_score_var.set("")
        self._refresh_recorded_grades()


class ClassOverviewTab(ttk.Frame):
    """Read-only view of every grade recorded for a class, from every course
    teacher assigned to it - visible to any teacher linked to that class."""

    def __init__(self, parent, db, teacher):
        super().__init__(parent)
        self.db = db
        self.teacher = teacher
        self._build_ui()
        self.refresh_class_list()

    def _build_ui(self):
        top = ttk.Frame(self)
        top.pack(fill="x", padx=10, pady=8)
        ttk.Label(top, text="Class:").pack(side="left")
        self.class_var = tk.StringVar()
        self.class_combo = ttk.Combobox(top, textvariable=self.class_var, state="readonly", width=20)
        self.class_combo.pack(side="left", padx=6)
        ttk.Button(top, text="View Grades", command=self.view_grades).pack(side="left", padx=6)
        ttk.Label(top, text="Shows every course/term recorded for this class (read-only).",
                  foreground="#666666").pack(side="left", padx=10)

        table_frame = ttk.Frame(self)
        table_frame.pack(fill="both", expand=True, padx=10, pady=8)
        cols = ("student", "course", "term", "class_score", "exam_score", "total", "grade", "remark")
        self.tree = ttk.Treeview(table_frame, columns=cols, show="headings", selectmode="browse")
        headers = ["Student", "Course", "Term", "Class/50", "Exam/50", "Total", "Grade", "Remark"]
        widths = [130, 110, 90, 65, 65, 60, 55, 100]
        for c, h, w in zip(cols, headers, widths):
            self.tree.heading(c, text=h)
            self.tree.column(c, width=w, anchor="center")
        vsb = ttk.Scrollbar(table_frame, orient="vertical", command=self.tree.yview)
        self.tree.configure(yscrollcommand=vsb.set)
        self.tree.pack(side="left", fill="both", expand=True)
        vsb.pack(side="right", fill="y")

    def refresh_class_list(self):
        classes = get_teacher_classes(self.db, self.teacher)
        self.class_combo["values"] = classes
        if classes and not self.class_var.get():
            self.class_var.set(classes[0])

    def view_grades(self):
        for row in self.tree.get_children():
            self.tree.delete(row)
        cls = self.class_var.get()
        if not cls:
            messagebox.showinfo("No class", "You are not currently linked to any class.")
            return
        rows = self.db.run(
            "SELECT s.name, g.subject, g.term, g.class_score_converted, g.exam_score_converted, "
            "g.score, g.grade, g.remark "
            "FROM grades g JOIN students s ON g.student_id = s.id "
            "WHERE s.student_class=? ORDER BY s.name, g.term, g.subject",
            (cls,),
        ).fetchall()
        if not rows:
            messagebox.showinfo("No grades yet", f"No grades have been recorded for {cls} yet.")
        for name, subject, term, class_conv, exam_conv, total, grade, remark in rows:
            class_str = f"{class_conv:.1f}" if class_conv is not None else "-"
            exam_str = f"{exam_conv:.1f}" if exam_conv is not None else "-"
            self.tree.insert("", "end", values=(name, subject, term, class_str, exam_str, f"{total:.1f}", grade, remark))


class ResultsSlipTab(ttk.Frame):
    """Only usable by the class's designated Class Teacher: compiles every
    course's grades (plus the student's passport photo) into one slip and
    can email it home."""

    def __init__(self, parent, db, teacher):
        super().__init__(parent)
        self.db = db
        self.teacher = teacher
        self.selected_student_id = None
        self._build_ui()

    def _build_ui(self):
        if not self.teacher.get("assigned_class"):
            ttk.Label(
                self,
                text=("Only the designated Class Teacher for a class can compile and send its "
                      "students' consolidated results slips.\n\nYou are not currently assigned as a "
                      "Class Teacher. Ask the Admin to assign you to a class if this should change."),
                foreground="#b30000", wraplength=520, justify="left", font=("Segoe UI", 10),
            ).pack(padx=20, pady=30)
            return

        ttk.Label(self, text=f"You are the Class Teacher of {self.teacher['assigned_class']}.",
                  font=("Segoe UI", 10, "bold")).pack(anchor="w", padx=14, pady=(10, 4))
        main = ttk.Frame(self)
        main.pack(fill="both", expand=True, padx=10, pady=8)

        left = ttk.LabelFrame(main, text=f"Students in {self.teacher['assigned_class']}")
        left.pack(side="left", fill="both", expand=True, padx=(0, 8))
        cols = ("id", "name", "dob", "hometown")
        self.tree = ttk.Treeview(left, columns=cols, show="headings", selectmode="browse", height=14)
        for c, h, w in zip(cols, ["ID", "Name", "DOB", "Hometown"], [40, 150, 100, 120]):
            self.tree.heading(c, text=h)
            self.tree.column(c, width=w, anchor="center")
        self.tree.pack(fill="both", expand=True, padx=6, pady=6)
        self.tree.bind("<<TreeviewSelect>>", self.on_student_select)

        right = ttk.LabelFrame(main, text="Compile Results Slip")
        right.pack(side="left", fill="both", expand=True)
        ttk.Label(right, text="Selected Student:").grid(row=0, column=0, sticky="e", padx=4, pady=8)
        self.selected_name_var = tk.StringVar(value="(none selected)")
        ttk.Label(right, textvariable=self.selected_name_var, font=("Segoe UI", 10, "bold")).grid(
            row=0, column=1, sticky="w", padx=4, pady=8
        )
        ttk.Label(right, text="Term:").grid(row=1, column=0, sticky="e", padx=4, pady=8)
        self.term_var = tk.StringVar(value=TERMS[0])
        ttk.Combobox(right, textvariable=self.term_var, values=TERMS, state="readonly", width=18).grid(
            row=1, column=1, sticky="w", padx=4, pady=8
        )
        ttk.Button(right, text="Generate, Preview & Send", command=self.generate_slip).grid(
            row=2, column=0, columnspan=2, pady=16
        )
        ttk.Label(
            right,
            text="Compiles grades from every course the student takes, entered by all their subject "
                 "teachers, and includes the student's passport photo on the PDF version.",
            foreground="#666666", wraplength=280, justify="left",
        ).grid(row=3, column=0, columnspan=2, padx=4)
        self.refresh_students()

    def refresh_students(self):
        if not self.teacher.get("assigned_class"):
            return
        for row in self.tree.get_children():
            self.tree.delete(row)
        rows = self.db.run(
            "SELECT id, name, COALESCE(dob,''), COALESCE(hometown,'') FROM students "
            "WHERE student_class=? ORDER BY name",
            (self.teacher["assigned_class"],),
        ).fetchall()
        for row in rows:
            self.tree.insert("", "end", values=row)

    def on_student_select(self, _event=None):
        sel = self.tree.selection()
        if not sel:
            return
        values = self.tree.item(sel[0], "values")
        self.selected_student_id = values[0]
        self.selected_name_var.set(values[1])

    def generate_slip(self):
        if not self.selected_student_id:
            messagebox.showwarning("No selection", "Select a student from the list first.")
            return
        open_slip_window(self, self.db, self.selected_student_id, self.term_var.get(), allow_email=True)


class TeacherTimetableTab(ttk.Frame):
    """View-only timetable access for any teacher linked to a class."""

    def __init__(self, parent, db, teacher):
        super().__init__(parent)
        self.db = db
        self.teacher = teacher
        self._build_ui()

    def _build_ui(self):
        classes = get_teacher_classes(self.db, self.teacher)
        if not classes:
            ttk.Label(self, text="You are not currently linked to any class.", foreground="#666666").pack(padx=20, pady=30)
            return
        top = ttk.Frame(self)
        top.pack(fill="x", padx=10, pady=20)
        ttk.Label(top, text="Class:").pack(side="left")
        self.class_var = tk.StringVar(value=classes[0])
        ttk.Combobox(top, textvariable=self.class_var, values=classes, state="readonly", width=15).pack(side="left", padx=6)
        ttk.Button(top, text="View / Print Timetable", command=self.view_timetable).pack(side="left", padx=10)

    def view_timetable(self):
        open_timetable_window(self, self.db, self.class_var.get())


class TeacherAttendanceTab(ttk.Frame):
    """Self-service clock-in. Available only from the opening time the Admin
    sets until 4:00 pm; the time is compared with the Admin's reporting time."""

    def __init__(self, parent, db, teacher):
        super().__init__(parent)
        self.db = db
        self.teacher = teacher
        self._build_ui()
        self.refresh()
        self._tick()

    def _build_ui(self):
        self.window_var = tk.StringVar()
        ttk.Label(self, textvariable=self.window_var, foreground="#555555").pack(anchor="w", padx=16, pady=(12, 0))
        top = ttk.Frame(self)
        top.pack(fill="x", padx=10, pady=10)
        self.status_var = tk.StringVar(value="Checking today's attendance...")
        ttk.Label(top, textvariable=self.status_var, font=("Segoe UI", 11, "bold")).pack(side="left", padx=6)
        self.clock_in_btn = ttk.Button(top, text="Clock In Now", command=self.clock_in)
        self.clock_in_btn.pack(side="left", padx=10)

        history_frame = ttk.LabelFrame(self, text="My Attendance History")
        history_frame.pack(fill="both", expand=True, padx=10, pady=8)
        cols = ("date", "time", "status")
        self.tree = ttk.Treeview(history_frame, columns=cols, show="headings", selectmode="browse")
        for c, h, w in zip(cols, ["Date", "Clock-in Time", "Status"], [120, 120, 100]):
            self.tree.heading(c, text=h)
            self.tree.column(c, width=w, anchor="center")
        self.tree.pack(fill="both", expand=True, padx=6, pady=6)

    def _times(self):
        return (get_setting(self.db, ATTENDANCE_OPEN_KEY, DEFAULT_ATTENDANCE_OPEN_TIME),
                get_setting(self.db, REPORTING_TIME_KEY, DEFAULT_REPORTING_TIME))

    def refresh(self):
        opens, reporting = self._times()
        window = attendance_window_state(datetime.now(), opens)
        self.window_var.set(
            f"Clock-in is available from {opens} until {CLOCK_IN_CLOSING_TIME} (4:00 pm). "
            f"Reporting time: {reporting}."
        )
        today = datetime.now().strftime("%Y-%m-%d")
        row = self.db.run(
            "SELECT clock_in_time, status FROM teacher_attendance WHERE teacher_id=? AND date=?",
            (self.teacher["id"], today),
        ).fetchone()
        if row:
            self.status_var.set(f"Today: clocked in at {row[0]} ({row[1]})")
            self.clock_in_btn.config(state="disabled")
        elif window == "before":
            self.status_var.set(f"Clock-in is not open yet - it opens at {opens}.")
            self.clock_in_btn.config(state="disabled")
        elif window == "after":
            self.status_var.set("Clock-in has closed for today.")
            self.clock_in_btn.config(state="disabled")
        else:
            self.status_var.set("You have not clocked in today.")
            self.clock_in_btn.config(state="normal")

        for r in self.tree.get_children():
            self.tree.delete(r)
        rows = self.db.run(
            "SELECT date, clock_in_time, status FROM teacher_attendance WHERE teacher_id=? ORDER BY date DESC",
            (self.teacher["id"],),
        ).fetchall()
        for r in rows:
            self.tree.insert("", "end", values=r)

    def _tick(self):
        """Re-check the window every 30 s so the button opens/closes on time."""
        try:
            self.refresh()
            self.after(30000, self._tick)
        except tk.TclError:
            pass                     # tab destroyed (logout)

    def clock_in(self):
        now = datetime.now()
        opens, reporting = self._times()
        window = attendance_window_state(now, opens)
        if window == "before":
            messagebox.showwarning("Too early", f"Clock-in opens at {opens}.")
            self.refresh()
            return
        if window == "after":
            messagebox.showwarning("Closed", f"Clock-in closed at {CLOCK_IN_CLOSING_TIME} (4:00 pm).")
            self.refresh()
            return
        today, time_str = now.strftime("%Y-%m-%d"), now.strftime("%H:%M:%S")
        status = compute_attendance_status(time_str, reporting)
        try:
            self.db.run(
                "INSERT INTO teacher_attendance (teacher_id, date, clock_in_time, status) VALUES (?, ?, ?, ?)",
                (self.teacher["id"], today, time_str, status),
                commit=True,
            )
            messagebox.showinfo("Clocked In", f"Clocked in at {time_str} - {status} (reporting time: {reporting}).")
        except sqlite3.IntegrityError:
            messagebox.showinfo("Already clocked in", "You've already clocked in today.")
        self.refresh()


class StudentAttendanceTab(ttk.Frame):
    """Daily attendance for a class, taken by that class's Class Teacher only."""

    def __init__(self, parent, db, teacher):
        super().__init__(parent)
        self.db = db
        self.teacher = teacher
        self.selected_student_id = None
        self._build_ui()

    def _build_ui(self):
        if not self.teacher.get("assigned_class"):
            ttk.Label(
                self,
                text=("Only the designated Class Teacher for a class can take its daily attendance.\n\n"
                      "You are not currently assigned as a Class Teacher."),
                foreground="#b30000", wraplength=520, justify="left", font=("Segoe UI", 10),
            ).pack(padx=20, pady=30)
            return

        top = ttk.Frame(self)
        top.pack(fill="x", padx=10, pady=10)
        ttk.Label(top, text=f"Class: {self.teacher['assigned_class']}    Date:").pack(side="left")
        self.date_var = tk.StringVar(value=datetime.now().strftime("%Y-%m-%d"))
        ttk.Entry(top, textvariable=self.date_var, width=14).pack(side="left", padx=6)
        ttk.Button(top, text="Load", command=self.refresh_students).pack(side="left", padx=6)
        ttk.Button(top, text="Mark All Present", command=self.mark_all_present).pack(side="left", padx=10)

        main = ttk.Frame(self)
        main.pack(fill="both", expand=True, padx=10, pady=8)
        cols = ("id", "name", "status")
        self.tree = ttk.Treeview(main, columns=cols, show="headings", selectmode="browse", height=14)
        for c, h, w in zip(cols, ["ID", "Name", "Status"], [40, 170, 110]):
            self.tree.heading(c, text=h)
            self.tree.column(c, width=w, anchor="center")
        self.tree.pack(side="left", fill="both", expand=True, padx=6, pady=6)
        self.tree.bind("<<TreeviewSelect>>", self.on_student_select)

        form = ttk.Frame(main)
        form.pack(side="left", fill="y", padx=10)
        ttk.Label(form, text="Selected Student:").pack(anchor="w", pady=4)
        self.selected_name_var = tk.StringVar(value="(none selected)")
        ttk.Label(form, textvariable=self.selected_name_var, font=("Segoe UI", 10, "bold")).pack(anchor="w")
        ttk.Label(form, text="Status:").pack(anchor="w", pady=(10, 2))
        self.mark_status_var = tk.StringVar(value=ATTENDANCE_STATUSES[0])
        ttk.Combobox(form, textvariable=self.mark_status_var, values=ATTENDANCE_STATUSES,
                     state="readonly", width=15).pack(anchor="w")
        ttk.Button(form, text="Save Status", command=self.save_status).pack(anchor="w", pady=10)
        self.refresh_students()

    def refresh_students(self):
        for r in self.tree.get_children():
            self.tree.delete(r)
        rows = self.db.run(
            "SELECT s.id, s.name, COALESCE(sa.status, '(not marked)') FROM students s "
            "LEFT JOIN student_attendance sa ON sa.student_id = s.id AND sa.date=? "
            "WHERE s.student_class=? ORDER BY s.name",
            (self.date_var.get().strip(), self.teacher["assigned_class"]),
        ).fetchall()
        for row in rows:
            self.tree.insert("", "end", values=row)

    def on_student_select(self, _event=None):
        sel = self.tree.selection()
        if not sel:
            return
        values = self.tree.item(sel[0], "values")
        self.selected_student_id = values[0]
        self.selected_name_var.set(values[1])
        if values[2] in ATTENDANCE_STATUSES:
            self.mark_status_var.set(values[2])

    def _upsert(self, student_id, d, status):
        self.db.run(
            "INSERT INTO student_attendance (student_id, date, status, recorded_by) VALUES (?, ?, ?, ?) "
            "ON CONFLICT(student_id, date) DO UPDATE SET status=excluded.status, recorded_by=excluded.recorded_by",
            (student_id, d, status, self.teacher["id"]),
            commit=True,
        )

    def save_status(self):
        if not self.selected_student_id:
            messagebox.showwarning("No selection", "Select a student first.")
            return
        d = self.date_var.get().strip()
        if not d:
            messagebox.showerror("Validation error", "Enter a date.")
            return
        self._upsert(self.selected_student_id, d, self.mark_status_var.get())
        self.refresh_students()

    def mark_all_present(self):
        d = self.date_var.get().strip()
        if not d:
            messagebox.showerror("Validation error", "Enter a date.")
            return
        for (sid,) in self.db.run("SELECT id FROM students WHERE student_class=?",
                                  (self.teacher["assigned_class"],)).fetchall():
            self._upsert(sid, d, "Present")
        self.refresh_students()


# ----------------------------------------------------------------------
# Parent dashboard (portal)
# ----------------------------------------------------------------------
def _children_tree(parent, height=10, title="My Children"):
    """Shared 'my children' list used by several parent tabs."""
    frame = ttk.LabelFrame(parent, text=title)
    cols = ("id", "name", "class")
    tree = ttk.Treeview(frame, columns=cols, show="headings", selectmode="browse", height=height)
    for c, h, w in zip(cols, ["ID", "Name", "Class"], [40, 160, 100]):
        tree.heading(c, text=h)
        tree.column(c, width=w, anchor="center")
    tree.pack(fill="both", expand=True, padx=6, pady=6)
    return frame, tree


def _load_children(db, tree, parent_id):
    for row in tree.get_children():
        tree.delete(row)
    rows = db.run(
        "SELECT id, name, student_class FROM students WHERE parent_id=? ORDER BY name", (parent_id,)
    ).fetchall()
    for row in rows:
        tree.insert("", "end", values=row)
    return rows


class ParentResultsTab(ttk.Frame):
    def __init__(self, parent, db, parent_user):
        super().__init__(parent)
        self.db = db
        self.parent_user = parent_user
        self.selected_student_id = None
        self._build_ui()
        self.refresh_children(notify=True)

    def _build_ui(self):
        main = ttk.Frame(self)
        main.pack(fill="both", expand=True, padx=10, pady=8)
        left, self.tree = _children_tree(main, height=12)
        left.pack(side="left", fill="both", expand=True, padx=(0, 8))
        self.tree.bind("<<TreeviewSelect>>", self.on_student_select)

        right = ttk.LabelFrame(main, text="View Results")
        right.pack(side="left", fill="both", expand=True)
        ttk.Label(right, text="Selected Child:").grid(row=0, column=0, sticky="e", padx=4, pady=8)
        self.selected_name_var = tk.StringVar(value="(none selected)")
        ttk.Label(right, textvariable=self.selected_name_var, font=("Segoe UI", 10, "bold")).grid(
            row=0, column=1, sticky="w", padx=4, pady=8
        )
        ttk.Label(right, text="Term:").grid(row=1, column=0, sticky="e", padx=4, pady=8)
        self.term_var = tk.StringVar(value=TERMS[0])
        ttk.Combobox(right, textvariable=self.term_var, values=TERMS, state="readonly", width=18).grid(
            row=1, column=1, sticky="w", padx=4, pady=8
        )
        ttk.Button(right, text="View / Print Results Slip", command=self.view_results).grid(
            row=2, column=0, columnspan=2, pady=16
        )
        ttk.Label(
            right, text="Opens a preview (with your child's photo) you can save as a PDF (or .txt) to print.",
            foreground="#666666", wraplength=260, justify="left",
        ).grid(row=3, column=0, columnspan=2, padx=4)

    def refresh_children(self, notify=False):
        rows = _load_children(self.db, self.tree, self.parent_user["id"])
        if notify and not rows:
            messagebox.showinfo(
                "No linked children",
                "No student records are linked to your account yet. Please contact the school Admin.",
            )

    def on_student_select(self, _event=None):
        sel = self.tree.selection()
        if not sel:
            return
        values = self.tree.item(sel[0], "values")
        self.selected_student_id = values[0]
        self.selected_name_var.set(values[1])

    def view_results(self):
        if not self.selected_student_id:
            messagebox.showwarning("No selection", "Select a child from the list first.")
            return
        open_slip_window(self, self.db, self.selected_student_id, self.term_var.get(), allow_email=False)


class ParentAnnouncementsTab(ttk.Frame):
    def __init__(self, parent, db, parent_user):
        super().__init__(parent)
        self.db = db
        self.parent_user = parent_user
        self._lookup = {}
        self._build_ui()
        self.refresh()

    def _build_ui(self):
        table_frame = ttk.Frame(self)
        table_frame.pack(fill="both", expand=True, padx=10, pady=8)
        cols = ("date", "title", "from")
        self.tree = ttk.Treeview(table_frame, columns=cols, show="headings", selectmode="browse")
        for c, h, w in zip(cols, ["Date", "Title", "From"], [140, 240, 160]):
            self.tree.heading(c, text=h)
            self.tree.column(c, width=w, anchor="center")
        vsb = ttk.Scrollbar(table_frame, orient="vertical", command=self.tree.yview)
        self.tree.configure(yscrollcommand=vsb.set)
        self.tree.pack(side="left", fill="both", expand=True)
        vsb.pack(side="right", fill="y")
        self.tree.bind("<<TreeviewSelect>>", self.on_select)

        ttk.Label(self, text="Message:", font=("Segoe UI", 9, "bold")).pack(anchor="w", padx=10)
        self.detail_text = tk.Text(self, height=8, wrap="word")
        self.detail_text.pack(fill="both", expand=False, padx=10, pady=(0, 10))
        self.detail_text.config(state="disabled")

    def refresh(self):
        for row in self.tree.get_children():
            self.tree.delete(row)
        rows = self.db.run(
            """
            SELECT id, created_at, title, body, sender_role, sender_name FROM announcements
            WHERE audience_type='all'
               OR (audience_type='class' AND audience_value IN
                   (SELECT DISTINCT student_class FROM students WHERE parent_id=?))
               OR (audience_type='student' AND audience_value IN
                   (SELECT CAST(id AS TEXT) FROM students WHERE parent_id=?))
            ORDER BY created_at DESC
            """,
            (self.parent_user["id"], self.parent_user["id"]),
        ).fetchall()
        self._lookup = {}
        for aid, created_at, title, body, srole, sname in rows:
            when = created_at[:16].replace("T", " ")
            iid = str(aid)
            self.tree.insert("", "end", iid=iid, values=(when, title, f"{sname} ({srole})"))
            self._lookup[iid] = body

    def on_select(self, _event=None):
        sel = self.tree.selection()
        if not sel:
            return
        self.detail_text.config(state="normal")
        self.detail_text.delete("1.0", "end")
        self.detail_text.insert("1.0", self._lookup.get(sel[0], ""))
        self.detail_text.config(state="disabled")


class ParentTimetableTab(ttk.Frame):
    def __init__(self, parent, db, parent_user):
        super().__init__(parent)
        self.db = db
        self.parent_user = parent_user
        self._build_ui()

    def _build_ui(self):
        rows = self.db.run(
            "SELECT DISTINCT student_class FROM students WHERE parent_id=?", (self.parent_user["id"],)
        ).fetchall()
        classes = sorted({r[0] for r in rows}, key=lambda c: CLASSES.index(c) if c in CLASSES else 99)
        if not classes:
            ttk.Label(self, text="No linked children yet.", foreground="#666666").pack(padx=20, pady=30)
            return
        top = ttk.Frame(self)
        top.pack(fill="x", padx=10, pady=20)
        ttk.Label(top, text="Child's Class:").pack(side="left")
        self.class_var = tk.StringVar(value=classes[0])
        ttk.Combobox(top, textvariable=self.class_var, values=classes, state="readonly", width=15).pack(side="left", padx=6)
        ttk.Button(top, text="View / Print Timetable", command=self.view_timetable).pack(side="left", padx=10)

    def view_timetable(self):
        open_timetable_window(self, self.db, self.class_var.get())


class ParentFeesTab(ttk.Frame):
    def __init__(self, parent, db, parent_user):
        super().__init__(parent)
        self.db = db
        self.parent_user = parent_user
        self.selected_student_id = None
        self._build_ui()
        self.refresh_children()

    def _build_ui(self):
        main = ttk.Frame(self)
        main.pack(fill="both", expand=True, padx=10, pady=8)
        left, self.tree = _children_tree(main)
        left.pack(side="left", fill="both", expand=True, padx=(0, 8))
        self.tree.bind("<<TreeviewSelect>>", self.on_student_select)

        right = ttk.LabelFrame(main, text="Fees")
        right.pack(side="left", fill="both", expand=True)
        top = ttk.Frame(right)
        top.pack(fill="x", padx=6, pady=6)
        ttk.Label(top, text="Term:").pack(side="left")
        self.term_var = tk.StringVar(value=TERMS[0])
        term_combo = ttk.Combobox(top, textvariable=self.term_var, values=TERMS, state="readonly", width=16)
        term_combo.pack(side="left", padx=6)
        term_combo.bind("<<ComboboxSelected>>", lambda e: self.refresh_summary())
        self.summary_var = tk.StringVar(value="Amount Due: -    Amount Paid: -    Balance: -")
        ttk.Label(right, textvariable=self.summary_var, font=("Segoe UI", 10, "bold")).pack(anchor="w", padx=6, pady=(0, 8))
        cols2 = ("date", "amount", "method", "note")
        self.history_tree = ttk.Treeview(right, columns=cols2, show="headings", selectmode="browse")
        for c, h, w in zip(cols2, ["Date", "Amount", "Method", "Note"], [100, 80, 110, 180]):
            self.history_tree.heading(c, text=h)
            self.history_tree.column(c, width=w, anchor="center")
        self.history_tree.pack(fill="both", expand=True, padx=6, pady=6)

    def refresh_children(self):
        _load_children(self.db, self.tree, self.parent_user["id"])

    def on_student_select(self, _event=None):
        sel = self.tree.selection()
        if not sel:
            return
        self.selected_student_id = self.tree.item(sel[0], "values")[0]
        self.refresh_summary()

    def refresh_summary(self):
        if not self.selected_student_id:
            return
        due, paid, balance = compute_fee_balance(self.db, self.selected_student_id, self.term_var.get())
        self.summary_var.set(f"Amount Due: {due:.2f}    Amount Paid: {paid:.2f}    Balance: {balance:.2f}")
        for r in self.history_tree.get_children():
            self.history_tree.delete(r)
        rows = self.db.run(
            "SELECT payment_date, amount_paid, method, COALESCE(note,'') FROM fee_payments "
            "WHERE student_id=? AND term=? ORDER BY payment_date DESC",
            (self.selected_student_id, self.term_var.get()),
        ).fetchall()
        for row in rows:
            self.history_tree.insert("", "end", values=row)


class ParentAttendanceTab(ttk.Frame):
    def __init__(self, parent, db, parent_user):
        super().__init__(parent)
        self.db = db
        self.parent_user = parent_user
        self.selected_student_id = None
        self._build_ui()
        self.refresh_children()

    def _build_ui(self):
        main = ttk.Frame(self)
        main.pack(fill="both", expand=True, padx=10, pady=8)
        left, self.tree = _children_tree(main)
        left.pack(side="left", fill="both", expand=True, padx=(0, 8))
        self.tree.bind("<<TreeviewSelect>>", self.on_student_select)

        right = ttk.LabelFrame(main, text="Attendance History")
        right.pack(side="left", fill="both", expand=True)
        cols2 = ("date", "status")
        self.history_tree = ttk.Treeview(right, columns=cols2, show="headings", selectmode="browse")
        for c, h, w in zip(cols2, ["Date", "Status"], [130, 110]):
            self.history_tree.heading(c, text=h)
            self.history_tree.column(c, width=w, anchor="center")
        self.history_tree.pack(fill="both", expand=True, padx=6, pady=6)

    def refresh_children(self):
        _load_children(self.db, self.tree, self.parent_user["id"])

    def on_student_select(self, _event=None):
        sel = self.tree.selection()
        if not sel:
            return
        self.selected_student_id = self.tree.item(sel[0], "values")[0]
        self.refresh_history()

    def refresh_history(self):
        for r in self.history_tree.get_children():
            self.history_tree.delete(r)
        if not self.selected_student_id:
            return
        rows = self.db.run(
            "SELECT date, status FROM student_attendance WHERE student_id=? ORDER BY date DESC",
            (self.selected_student_id,),
        ).fetchall()
        for row in rows:
            self.history_tree.insert("", "end", values=row)


class ParentDashboard(ttk.Frame):
    def __init__(self, parent, controller):
        super().__init__(parent)
        self.controller = controller
        self.db = controller.db
        self.parent_user = controller.current_user

        TopBar(self, controller, "Parent Portal").pack(fill="x")

        notebook = ttk.Notebook(self)
        notebook.pack(fill="both", expand=True, padx=10, pady=8)

        self.results_tab = ParentResultsTab(notebook, self.db, self.parent_user)
        self.announcements_tab = ParentAnnouncementsTab(notebook, self.db, self.parent_user)
        self.timetable_tab = ParentTimetableTab(notebook, self.db, self.parent_user)
        self.fees_tab = ParentFeesTab(notebook, self.db, self.parent_user)
        self.attendance_tab = ParentAttendanceTab(notebook, self.db, self.parent_user)

        notebook.add(self.results_tab, text="My Children & Results")
        notebook.add(self.announcements_tab, text="Announcements")
        notebook.add(self.timetable_tab, text="Class Timetable")
        notebook.add(self.fees_tab, text="Fees")
        notebook.add(self.attendance_tab, text="Attendance")

        notebook.bind("<<NotebookTabChanged>>", self._on_tab_changed)

    def _on_tab_changed(self, _event=None):
        self.results_tab.refresh_children()
        self.announcements_tab.refresh()
        self.fees_tab.refresh_children()
        self.fees_tab.refresh_summary()
        self.attendance_tab.refresh_children()
        self.attendance_tab.refresh_history()

    def refresh_all(self):
        """Called after a network sync brought in changes from other devices."""
        self._on_tab_changed()


# ----------------------------------------------------------------------
# Main application controller
# ----------------------------------------------------------------------
class App(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title(f"{SCHOOL_NAME} - School Management System")
        self.geometry("1250x720")
        self.minsize(1000, 620)

        try:
            style = ttk.Style(self)
            if "clam" in style.theme_names():
                style.theme_use("clam")
        except tk.TclError:
            pass

        self.db = Database()
        self.current_user = None
        self.sync = SyncManager(self.db, self, on_applied=self._on_sync_applied)

        # Sync status strip along the bottom of every screen.
        self.sync_status_var = tk.StringVar()
        ttk.Label(self, textvariable=self.sync_status_var, relief="sunken", anchor="w",
                  padding=(8, 2)).pack(side="bottom", fill="x")
        self.container = ttk.Frame(self)
        self.container.pack(fill="both", expand=True)

        self._update_sync_status()
        self.show_login()
        self.sync.start_auto()

    def _update_sync_status(self):
        self.sync_status_var.set(self.sync.status_summary())
        self.after(2000, self._update_sync_status)

    def _on_sync_applied(self):
        """Changes arrived from other devices: refresh whatever screen is showing."""
        for widget in self.container.winfo_children():
            if hasattr(widget, "refresh_all"):
                widget.refresh_all()

    def _clear_container(self):
        for widget in self.container.winfo_children():
            widget.destroy()

    def show_login(self):
        self._clear_container()
        LoginFrame(self.container, self).pack(fill="both", expand=True)

    def show_admin_dashboard(self):
        self._clear_container()
        AdminDashboard(self.container, self).pack(fill="both", expand=True)

    def show_teacher_dashboard(self):
        self._clear_container()
        TeacherDashboard(self.container, self).pack(fill="both", expand=True)

    def show_parent_dashboard(self):
        self._clear_container()
        ParentDashboard(self.container, self).pack(fill="both", expand=True)

    def logout(self):
        self.current_user = None
        self.show_login()


if __name__ == "__main__":
    app = App()
    app.mainloop()