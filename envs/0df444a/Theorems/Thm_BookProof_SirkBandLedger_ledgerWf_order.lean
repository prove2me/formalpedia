-- Prove2me | Theorems.Thm_BookProof_SirkBandLedger_ledgerWf_order
-- name    : BookProof.SirkBandLedger.ledgerWf_order
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T12:06:03.813569+00:00
-- url     : https://prove2.me/theorems/f2042e0a-813a-4f78-a93b-b26e4c3db820
-- title:
--   {L : List BandRecord} (h : LedgerWf L) {i : ℕ} (hi : i < L.length) : (L.getD i default).order = i
-- statement:
--   Lean 4 theorem `BookProof.SirkBandLedger.ledgerWf_order` (module `BookProof.SirkBandLedger`), source chapter `BookProof/ChapterSirkBandLedger.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterSirkBandLedger.lean

-- Generated from ChapterSirkBandLedger.lean — theorem BookProof.SirkBandLedger.ledgerWf_order
import Mathlib
import Definitions.Def_ChapterSirkBandLedger
open BookProof.SirkBandLedger















open BookProof.SirkCertificateReader
open BookProof.BandEnclosure

theorem BookProof.SirkBandLedger.ledgerWf_order {L : List BandRecord} (h : LedgerWf L) {i : ℕ}
    (hi : i < L.length) : (L.getD i default).order = i := by sorry
