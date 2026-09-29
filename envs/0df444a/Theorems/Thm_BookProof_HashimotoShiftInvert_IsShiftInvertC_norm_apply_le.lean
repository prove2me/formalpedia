-- Prove2me | Theorems.Thm_BookProof_HashimotoShiftInvert_IsShiftInvertC_norm_apply_le
-- name    : BookProof.HashimotoShiftInvert.IsShiftInvertC.norm_apply_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T19:23:57.930529+00:00
-- url     : https://prove2.me/theorems/9173d4f6-8379-42b3-8cb5-81c664a55a2a
-- title:
--   The Lean 4 theorem `norm_apply_le` in the `ChapterHashimotoComplexShifts` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `norm_apply_le` in the `ChapterHashimotoComplexShifts` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHashimotoComplexShifts.lean

-- Generated from ChapterHashimotoComplexShifts.lean — theorem BookProof.HashimotoShiftInvert.IsShiftInvertC.norm_apply_le
import Mathlib
import Definitions.Def_ChapterHashimotoComplexShifts
open BookProof.HashimotoShiftInvert


















open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit
open BookProof.HermiteGalerkin
open Filter Topology




variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {Dom : Submodule ℂ F}

theorem BookProof.HashimotoShiftInvert.IsShiftInvertC.norm_apply_le {A : Dom →ₗ[ℂ] F} {γ : ℂ} {X : F →L[ℂ] F}
    (h : IsShiftInvertC A γ X) (hsym : SymmetricOn Dom A) (hγ : γ.im ≠ 0) (u : F) :
    ‖X u‖ ≤ |γ.im|⁻¹ * ‖u‖ := by sorry
