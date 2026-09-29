-- Prove2me | Theorems.Thm_BookProof_HashimotoShiftInvert_rkVec_succ
-- name    : BookProof.HashimotoShiftInvert.rkVec_succ
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T18:22:50.314403+00:00
-- url     : https://prove2.me/theorems/c1021004-1c8e-4121-bee7-42d9dcd20b66
-- title:
--   The Lean 4 theorem `rkVec_succ` in the `ChapterHashimotoComplexShifts` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `rkVec_succ` in the `ChapterHashimotoComplexShifts` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHashimotoComplexShifts.lean

-- Generated from ChapterHashimotoComplexShifts.lean — theorem BookProof.HashimotoShiftInvert.rkVec_succ
import Mathlib
import Definitions.Def_ChapterHashimotoComplexShifts
open BookProof.HashimotoShiftInvert


















open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit
open BookProof.HermiteGalerkin
open Filter Topology




variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {Dom : Submodule ℂ F}


















variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {Dom : Submodule ℂ F}

theorem BookProof.HashimotoShiftInvert.rkVec_succ (X : ℕ → F →L[ℂ] F) (v : F) (k : ℕ) :
    rkVec X v (k + 1) = X k (rkVec X v k) := by sorry
