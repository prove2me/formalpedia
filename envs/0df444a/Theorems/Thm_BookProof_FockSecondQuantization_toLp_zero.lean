-- Prove2me | Theorems.Thm_BookProof_FockSecondQuantization_toLp_zero
-- name    : BookProof.FockSecondQuantization.toLp_zero
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T11:25:39.065051+00:00
-- url     : https://prove2.me/theorems/2abf37e4-19ba-4ee8-9bbb-acc756e0fddd
-- title:
--   : toLp (0 : FockAlg) = 0
-- statement:
--   Lean 4 theorem `BookProof.FockSecondQuantization.toLp_zero` (module `BookProof.FockSecondQuantization`), source chapter `BookProof/ChapterFockSecondQuantization.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterFockSecondQuantization.lean

-- Generated from ChapterFockSecondQuantization.lean — theorem BookProof.FockSecondQuantization.toLp_zero
import Mathlib
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockSecondQuantization







open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension
open BookProof.HashimotoShiftInvert

noncomputable section

theorem BookProof.FockSecondQuantization.toLp_zero : toLp (0 : FockAlg) = 0 := by sorry
