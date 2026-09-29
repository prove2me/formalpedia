-- Prove2me | Theorems.Thm_BookProof_HashimotoShiftInvert_isShiftInvertC_neg_of_isShiftInvert
-- name    : BookProof.HashimotoShiftInvert.isShiftInvertC_neg_of_isShiftInvert
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T19:24:02.203095+00:00
-- url     : https://prove2.me/theorems/ea9f15db-f507-490c-8a3f-e29f02760327
-- title:
--   The Lean 4 theorem `isShiftInvertC_neg_of_isShiftInvert` in the `ChapterHashimotoComplexShifts` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `isShiftInvertC_neg_of_isShiftInvert` in the `ChapterHashimotoComplexShifts` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHashimotoComplexShifts.lean

-- Generated from ChapterHashimotoComplexShifts.lean — theorem BookProof.HashimotoShiftInvert.isShiftInvertC_neg_of_isShiftInvert
import Mathlib
import Definitions.Def_ChapterHashimotoComplexShifts
open BookProof.HashimotoShiftInvert


















open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit
open BookProof.HermiteGalerkin
open Filter Topology




variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {Dom : Submodule ℂ F}

theorem BookProof.HashimotoShiftInvert.isShiftInvertC_neg_of_isShiftInvert {A : Dom →ₗ[ℂ] F} {c : ℝ} {R : F →L[ℂ] F}
    (h : IsShiftInvert A c R) : IsShiftInvertC A (-(c : ℂ)) (-R) := by sorry
