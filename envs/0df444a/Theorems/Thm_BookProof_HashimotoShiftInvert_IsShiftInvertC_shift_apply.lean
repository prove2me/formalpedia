-- Prove2me | Theorems.Thm_BookProof_HashimotoShiftInvert_IsShiftInvertC_shift_apply
-- name    : BookProof.HashimotoShiftInvert.IsShiftInvertC.shift_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T09:00:28.704864+00:00
-- url     : https://prove2.me/theorems/e85ca331-97c7-4394-8bc9-05aa48340198
-- title:
--   The Lean 4 theorem `shift_apply` in the `ChapterHashimotoComplexShifts` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `shift_apply` in the `ChapterHashimotoComplexShifts` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHashimotoComplexShifts.lean

-- Generated from ChapterHashimotoComplexShifts.lean — theorem BookProof.HashimotoShiftInvert.IsShiftInvertC.shift_apply
import Mathlib
import Definitions.Def_ChapterHashimotoComplexShifts
open BookProof.HashimotoShiftInvert


















open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit
open BookProof.HermiteGalerkin
open Filter Topology




variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {Dom : Submodule ℂ F}

theorem BookProof.HashimotoShiftInvert.IsShiftInvertC.shift_apply {A : Dom →ₗ[ℂ] F} {γ : ℂ} {X : F →L[ℂ] F}
    (h : IsShiftInvertC A γ X) (u : F) :
    γ • X u - A ⟨X u, (h.2 u).choose⟩ = u := by sorry
