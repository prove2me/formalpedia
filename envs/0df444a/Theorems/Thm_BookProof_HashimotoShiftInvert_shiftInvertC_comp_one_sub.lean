-- Prove2me | Theorems.Thm_BookProof_HashimotoShiftInvert_shiftInvertC_comp_one_sub
-- name    : BookProof.HashimotoShiftInvert.shiftInvertC_comp_one_sub
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:16:08.882416+00:00
-- url     : https://prove2.me/theorems/79ad4aee-2a8e-4f2e-b786-85fc8c556e8d
-- title:
--   The Lean 4 theorem `shiftInvertC_comp_one_sub` in the `ChapterHashimotoComplexShifts` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `shiftInvertC_comp_one_sub` in the `ChapterHashimotoComplexShifts` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHashimotoComplexShifts.lean

-- Generated from ChapterHashimotoComplexShifts.lean — theorem BookProof.HashimotoShiftInvert.shiftInvertC_comp_one_sub
import Mathlib
import Definitions.Def_ChapterHashimotoComplexShifts
open BookProof.HashimotoShiftInvert


















open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit
open BookProof.HermiteGalerkin
open Filter Topology




variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {Dom : Submodule ℂ F}


















variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {Dom : Submodule ℂ F}

theorem BookProof.HashimotoShiftInvert.shiftInvertC_comp_one_sub {A : Dom →ₗ[ℂ] F} {γ δ : ℂ} {X Y : F →L[ℂ] F}
    (hX : IsShiftInvertC A γ X) (hY : IsShiftInvertC A δ Y) :
    X ∘L (ContinuousLinearMap.id ℂ F - (δ - γ) • Y) = Y := by sorry
