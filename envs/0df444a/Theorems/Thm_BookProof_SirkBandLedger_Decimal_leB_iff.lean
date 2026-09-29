-- Prove2me | Theorems.Thm_BookProof_SirkBandLedger_Decimal_leB_iff
-- name    : BookProof.SirkBandLedger.Decimal.leB_iff
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T12:01:33.868159+00:00
-- url     : https://prove2.me/theorems/d02d1088-270f-4aa3-b920-36503c7acb5c
-- title:
--   (d e : Decimal) : Decimal.leB d e ↔ d.toQ ≤ e.toQ
-- statement:
--   Lean 4 theorem `BookProof.SirkBandLedger.Decimal.leB_iff` (module `BookProof.SirkBandLedger`), source chapter `BookProof/ChapterSirkBandLedger.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterSirkBandLedger.lean

-- Generated from ChapterSirkBandLedger.lean — theorem BookProof.SirkBandLedger.Decimal.leB_iff
import Mathlib
import Definitions.Def_ChapterSirkBandLedger
open BookProof.SirkBandLedger
open BookProof.SirkBandLedger.Decimal















open BookProof.SirkCertificateReader
open BookProof.BandEnclosure

theorem BookProof.SirkBandLedger.Decimal.leB_iff (d e : Decimal) : Decimal.leB d e ↔ d.toQ ≤ e.toQ := by sorry
