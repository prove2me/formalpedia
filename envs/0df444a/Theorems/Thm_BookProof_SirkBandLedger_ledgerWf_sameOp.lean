-- Prove2me | Theorems.Thm_BookProof_SirkBandLedger_ledgerWf_sameOp
-- name    : BookProof.SirkBandLedger.ledgerWf_sameOp
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T12:07:00.133425+00:00
-- url     : https://prove2.me/theorems/c744ebe5-07b2-44e1-9511-e3ee01e358ea
-- title:
--   {L : List BandRecord} (h : LedgerWf L) {r : BandRecord} (hr : r ∈ L) : r.op = (L.getD 0 default).op
-- statement:
--   Lean 4 theorem `BookProof.SirkBandLedger.ledgerWf_sameOp` (module `BookProof.SirkBandLedger`), source chapter `BookProof/ChapterSirkBandLedger.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterSirkBandLedger.lean

-- Generated from ChapterSirkBandLedger.lean — theorem BookProof.SirkBandLedger.ledgerWf_sameOp
import Mathlib
import Definitions.Def_ChapterSirkBandLedger
open BookProof.SirkBandLedger















open BookProof.SirkCertificateReader
open BookProof.BandEnclosure

theorem BookProof.SirkBandLedger.ledgerWf_sameOp {L : List BandRecord} (h : LedgerWf L) {r : BandRecord}
    (hr : r ∈ L) : r.op = (L.getD 0 default).op := by sorry
