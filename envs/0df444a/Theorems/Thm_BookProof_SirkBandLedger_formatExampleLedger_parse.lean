-- Prove2me | Theorems.Thm_BookProof_SirkBandLedger_formatExampleLedger_parse
-- name    : BookProof.SirkBandLedger.formatExampleLedger_parse
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T12:03:20.413384+00:00
-- url     : https://prove2.me/theorems/9b09cbf0-94d7-4f29-80ac-dc766100ee4e
-- title:
--   : parseLedger formatExampleLedgerNdjson = formatExampleLedger
-- statement:
--   Lean 4 theorem `BookProof.SirkBandLedger.formatExampleLedger_parse` (module `BookProof.SirkBandLedger`), source chapter `BookProof/ChapterSirkBandLedger.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterSirkBandLedger.lean

-- Generated from ChapterSirkBandLedger.lean — theorem BookProof.SirkBandLedger.formatExampleLedger_parse
import Mathlib
import Definitions.Def_ChapterSirkBandLedger
open BookProof.SirkBandLedger















open BookProof.SirkCertificateReader
open BookProof.BandEnclosure



































open BookProof.HermiteGalerkin BookProof.YangMillsFriedrichs
open BookProof.YangMillsFriedrichsLimit BookProof.ChapterSirkRitzSpectrum

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]




open BookProof.FarisLavine BookProof.HermiteGalerkin BookProof.YangMillsFriedrichs
open BookProof.HashimotoShiftInvert BookProof.FriedrichsExtension

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]






set_option maxRecDepth 10000

theorem BookProof.SirkBandLedger.formatExampleLedger_parse :
    parseLedger formatExampleLedgerNdjson = formatExampleLedger := by sorry
