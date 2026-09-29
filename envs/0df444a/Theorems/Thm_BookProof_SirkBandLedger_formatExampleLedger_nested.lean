-- Prove2me | Theorems.Thm_BookProof_SirkBandLedger_formatExampleLedger_nested
-- name    : BookProof.SirkBandLedger.formatExampleLedger_nested
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T12:18:50.91345+00:00
-- url     : https://prove2.me/theorems/5408dbc5-349e-4803-9984-18ba46c4faf8
-- title:
--   : NestedBands (ledgerLo formatExampleLedger) (ledgerHi formatExampleLedger)
-- statement:
--   Lean 4 theorem `BookProof.SirkBandLedger.formatExampleLedger_nested` (module `BookProof.SirkBandLedger`), source chapter `BookProof/ChapterSirkBandLedger.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterSirkBandLedger.lean

-- Generated from ChapterSirkBandLedger.lean — theorem BookProof.SirkBandLedger.formatExampleLedger_nested
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

theorem BookProof.SirkBandLedger.formatExampleLedger_nested :
    NestedBands (ledgerLo formatExampleLedger) (ledgerHi formatExampleLedger) := by sorry
