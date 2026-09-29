-- Prove2me | Theorems.Thm_BookProof_SirkBandLedger_ledgerWf_enclosing
-- name    : BookProof.SirkBandLedger.ledgerWf_enclosing
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T13:50:45.332053+00:00
-- url     : https://prove2.me/theorems/aaf5b1df-645b-449c-9687-6bb0a9ca171c
-- title:
--   {L : List BandRecord} (h : LedgerWf L) {r : BandRecord} (hr : r ∈ L) : r.lo.toQ ≤ r.hi.toQ
-- statement:
--   Lean 4 theorem `BookProof.SirkBandLedger.ledgerWf_enclosing` (module `BookProof.SirkBandLedger`), source chapter `BookProof/ChapterSirkBandLedger.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterSirkBandLedger.lean

-- Generated from ChapterSirkBandLedger.lean — theorem BookProof.SirkBandLedger.ledgerWf_enclosing
import Mathlib
import Definitions.Def_ChapterSirkBandLedger
open BookProof.SirkBandLedger















open BookProof.SirkCertificateReader
open BookProof.BandEnclosure

theorem BookProof.SirkBandLedger.ledgerWf_enclosing {L : List BandRecord} (h : LedgerWf L) {r : BandRecord}
    (hr : r ∈ L) : r.lo.toQ ≤ r.hi.toQ := by sorry
