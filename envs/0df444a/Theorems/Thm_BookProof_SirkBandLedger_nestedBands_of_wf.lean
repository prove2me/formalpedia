-- Prove2me | Theorems.Thm_BookProof_SirkBandLedger_nestedBands_of_wf
-- name    : BookProof.SirkBandLedger.nestedBands_of_wf
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T12:13:35.457342+00:00
-- url     : https://prove2.me/theorems/94d5f518-3cd4-459b-8736-814bf22f924a
-- title:
--   {L : List BandRecord} (h : LedgerWf L) : NestedBands (ledgerLo L) (ledgerHi L)
-- statement:
--   Lean 4 theorem `BookProof.SirkBandLedger.nestedBands_of_wf` (module `BookProof.SirkBandLedger`), source chapter `BookProof/ChapterSirkBandLedger.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterSirkBandLedger.lean

-- Generated from ChapterSirkBandLedger.lean — theorem BookProof.SirkBandLedger.nestedBands_of_wf
import Mathlib
import Definitions.Def_ChapterSirkBandLedger
open BookProof.SirkBandLedger















open BookProof.SirkCertificateReader
open BookProof.BandEnclosure

theorem BookProof.SirkBandLedger.nestedBands_of_wf {L : List BandRecord} (h : LedgerWf L) :
    NestedBands (ledgerLo L) (ledgerHi L) := by sorry
