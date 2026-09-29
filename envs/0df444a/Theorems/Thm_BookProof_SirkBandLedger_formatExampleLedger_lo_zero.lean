-- Prove2me | Theorems.Thm_BookProof_SirkBandLedger_formatExampleLedger_lo_zero
-- name    : BookProof.SirkBandLedger.formatExampleLedger_lo_zero
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T12:02:33.637364+00:00
-- url     : https://prove2.me/theorems/6489e23a-efe4-4a9c-80ac-619fe4c8a6e8
-- title:
--   : ledgerLo formatExampleLedger 0 = 0.9
-- statement:
--   Lean 4 theorem `BookProof.SirkBandLedger.formatExampleLedger_lo_zero` (module `BookProof.SirkBandLedger`), source chapter `BookProof/ChapterSirkBandLedger.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterSirkBandLedger.lean

-- Generated from ChapterSirkBandLedger.lean — theorem BookProof.SirkBandLedger.formatExampleLedger_lo_zero
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

theorem BookProof.SirkBandLedger.formatExampleLedger_lo_zero : ledgerLo formatExampleLedger 0 = 0.9 := by sorry
