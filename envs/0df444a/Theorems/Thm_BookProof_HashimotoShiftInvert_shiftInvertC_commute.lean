-- Prove2me | Theorems.Thm_BookProof_HashimotoShiftInvert_shiftInvertC_commute
-- name    : BookProof.HashimotoShiftInvert.shiftInvertC_commute
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:15:56.539981+00:00
-- url     : https://prove2.me/theorems/9d5910f0-182e-4e96-92bc-ce6cb6d16be8
-- title:
--   The Lean 4 theorem `shiftInvertC_commute` in the `ChapterHashimotoComplexShifts` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `shiftInvertC_commute` in the `ChapterHashimotoComplexShifts` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHashimotoComplexShifts.lean

-- Generated from ChapterHashimotoComplexShifts.lean — theorem BookProof.HashimotoShiftInvert.shiftInvertC_commute
import Mathlib
import Definitions.Def_ChapterHashimotoComplexShifts
open BookProof.HashimotoShiftInvert


















open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit
open BookProof.HermiteGalerkin
open Filter Topology




variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {Dom : Submodule ℂ F}


















variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {Dom : Submodule ℂ F}

theorem BookProof.HashimotoShiftInvert.shiftInvertC_commute {A : Dom →ₗ[ℂ] F} {γ δ : ℂ} {X Y : F →L[ℂ] F}
    (hX : IsShiftInvertC A γ X) (hY : IsShiftInvertC A δ Y) : X ∘L Y = Y ∘L X := by sorry
