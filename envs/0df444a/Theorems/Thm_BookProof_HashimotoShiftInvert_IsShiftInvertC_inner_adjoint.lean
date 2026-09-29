-- Prove2me | Theorems.Thm_BookProof_HashimotoShiftInvert_IsShiftInvertC_inner_adjoint
-- name    : BookProof.HashimotoShiftInvert.IsShiftInvertC.inner_adjoint
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T19:23:53.93266+00:00
-- url     : https://prove2.me/theorems/0d55ecc7-fdab-4a73-854d-b0cd26c0c174
-- title:
--   The Lean 4 theorem `inner_adjoint` in the `ChapterHashimotoComplexShifts` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `inner_adjoint` in the `ChapterHashimotoComplexShifts` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHashimotoComplexShifts.lean

-- Generated from ChapterHashimotoComplexShifts.lean — theorem BookProof.HashimotoShiftInvert.IsShiftInvertC.inner_adjoint
import Mathlib
import Definitions.Def_ChapterHashimotoComplexShifts
open BookProof.HashimotoShiftInvert


















open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit
open BookProof.HermiteGalerkin
open Filter Topology




variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {Dom : Submodule ℂ F}

theorem BookProof.HashimotoShiftInvert.IsShiftInvertC.inner_adjoint {A : Dom →ₗ[ℂ] F} {γ : ℂ} {X Y : F →L[ℂ] F}
    (hX : IsShiftInvertC A γ X) (hY : IsShiftInvertC A ((starRingEnd ℂ) γ) Y)
    (hsym : SymmetricOn Dom A) (u v : F) :
    (inner ℂ (X u) v : ℂ) = inner ℂ u (Y v) := by sorry
