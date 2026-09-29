-- Prove2me | Theorems.Thm_BookProof_HashimotoShiftInvert_IsShiftInvertC_injective
-- name    : BookProof.HashimotoShiftInvert.IsShiftInvertC.injective
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T19:23:22.162371+00:00
-- url     : https://prove2.me/theorems/fcd17e84-1cca-4ba6-bdfa-c061a9ce1533
-- title:
--   The Lean 4 theorem `injective` in the `ChapterHashimotoComplexShifts` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `injective` in the `ChapterHashimotoComplexShifts` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHashimotoComplexShifts.lean

-- Generated from ChapterHashimotoComplexShifts.lean — theorem BookProof.HashimotoShiftInvert.IsShiftInvertC.injective
import Mathlib
import Definitions.Def_ChapterHashimotoComplexShifts
open BookProof.HashimotoShiftInvert


















open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit
open BookProof.HermiteGalerkin
open Filter Topology




variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {Dom : Submodule ℂ F}

theorem BookProof.HashimotoShiftInvert.IsShiftInvertC.injective {A : Dom →ₗ[ℂ] F} {γ : ℂ} {X : F →L[ℂ] F}
    (h : IsShiftInvertC A γ X) : Function.Injective X := by sorry
