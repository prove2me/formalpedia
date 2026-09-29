-- Prove2me | Theorems.Thm_BookProof_HashimotoShiftInvert_rkVec_zero
-- name    : BookProof.HashimotoShiftInvert.rkVec_zero
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T18:22:35.847766+00:00
-- url     : https://prove2.me/theorems/6e4fc80a-27b0-4d08-bc0e-99f0d3534186
-- title:
--   The Lean 4 theorem `rkVec_zero` in the `ChapterHashimotoComplexShifts` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `rkVec_zero` in the `ChapterHashimotoComplexShifts` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHashimotoComplexShifts.lean

-- Generated from ChapterHashimotoComplexShifts.lean — theorem BookProof.HashimotoShiftInvert.rkVec_zero
import Mathlib
import Definitions.Def_ChapterHashimotoComplexShifts
open BookProof.HashimotoShiftInvert


















open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit
open BookProof.HermiteGalerkin
open Filter Topology




variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {Dom : Submodule ℂ F}


















variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {Dom : Submodule ℂ F}

theorem BookProof.HashimotoShiftInvert.rkVec_zero (X : ℕ → F →L[ℂ] F) (v : F) : rkVec X v 0 = v := by sorry
