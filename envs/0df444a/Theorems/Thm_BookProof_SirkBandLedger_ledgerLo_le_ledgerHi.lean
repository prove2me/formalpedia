-- Prove2me | Theorems.Thm_BookProof_SirkBandLedger_ledgerLo_le_ledgerHi
-- name    : BookProof.SirkBandLedger.ledgerLo_le_ledgerHi
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T14:31:07.712571+00:00
-- url     : https://prove2.me/theorems/c46d7770-8472-4c74-983a-262a07bcae92
-- title:
--   {L : List BandRecord} (h : LedgerWf L) (m : ℕ) : ledgerLo L m ≤ ledgerHi L m
-- statement:
--   Lean 4 theorem `BookProof.SirkBandLedger.ledgerLo_le_ledgerHi` (module `BookProof.SirkBandLedger`), source chapter `BookProof/ChapterSirkBandLedger.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterSirkBandLedger.lean

-- Generated from ChapterSirkBandLedger.lean — theorem BookProof.SirkBandLedger.ledgerLo_le_ledgerHi
import Mathlib
import Definitions.Def_ChapterSirkBandLedger
open BookProof.SirkBandLedger















open BookProof.SirkCertificateReader
open BookProof.BandEnclosure

theorem BookProof.SirkBandLedger.ledgerLo_le_ledgerHi {L : List BandRecord} (h : LedgerWf L) (m : ℕ) :
    ledgerLo L m ≤ ledgerHi L m := by sorry
