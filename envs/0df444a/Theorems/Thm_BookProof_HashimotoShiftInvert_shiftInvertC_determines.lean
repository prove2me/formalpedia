-- Prove2me | Theorems.Thm_BookProof_HashimotoShiftInvert_shiftInvertC_determines
-- name    : BookProof.HashimotoShiftInvert.shiftInvertC_determines
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:15:52.837658+00:00
-- url     : https://prove2.me/theorems/e197eb65-7fcb-48bf-850b-c43726984a2a
-- title:
--   The Lean 4 theorem `shiftInvertC_determines` in the `ChapterHashimotoComplexShifts` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `shiftInvertC_determines` in the `ChapterHashimotoComplexShifts` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHashimotoComplexShifts.lean

-- Generated from ChapterHashimotoComplexShifts.lean — theorem BookProof.HashimotoShiftInvert.shiftInvertC_determines
import Mathlib
import Definitions.Def_ChapterHashimotoComplexShifts
open BookProof.HashimotoShiftInvert


















open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit
open BookProof.HermiteGalerkin
open Filter Topology




variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {Dom : Submodule ℂ F}

theorem BookProof.HashimotoShiftInvert.shiftInvertC_determines {Dom₁ Dom₂ : Submodule ℂ F} {A₁ : Dom₁ →ₗ[ℂ] F}
    {A₂ : Dom₂ →ₗ[ℂ] F} {γ : ℂ} {X : F →L[ℂ] F}
    (h₁ : IsShiftInvertC A₁ γ X) (h₂ : IsShiftInvertC A₂ γ X) :
    Dom₁ = Dom₂ ∧ ∀ (x : F) (hx₁ : x ∈ Dom₁) (hx₂ : x ∈ Dom₂), A₁ ⟨x, hx₁⟩ = A₂ ⟨x, hx₂⟩ := by sorry
