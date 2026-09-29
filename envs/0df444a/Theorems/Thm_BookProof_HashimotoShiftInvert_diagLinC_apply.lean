-- Prove2me | Theorems.Thm_BookProof_HashimotoShiftInvert_diagLinC_apply
-- name    : BookProof.HashimotoShiftInvert.diagLinC_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:25:19.748682+00:00
-- url     : https://prove2.me/theorems/6c22f8b2-f6ce-4349-a880-692c54fd1d3d
-- title:
--   The Lean 4 theorem `diagLinC_apply` in the `ChapterHashimotoComplexShifts` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `diagLinC_apply` in the `ChapterHashimotoComplexShifts` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHashimotoComplexShifts.lean

-- Generated from ChapterHashimotoComplexShifts.lean — theorem BookProof.HashimotoShiftInvert.diagLinC_apply
import Mathlib
import Definitions.Def_ChapterHashimotoComplexShifts
open BookProof.HashimotoShiftInvert


















open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit
open BookProof.HermiteGalerkin
open Filter Topology




variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {Dom : Submodule ℂ F}


















variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {Dom : Submodule ℂ F}




















variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]







variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]








open scoped ENNReal InnerProductSpace lp

theorem BookProof.HashimotoShiftInvert.diagLinC_apply {c : ℕ → ℂ} {M : ℝ} (hc : ∀ n, ‖c n‖ ≤ M) (x : ℓ²(ℕ, ℂ)) (n : ℕ) :
    ((diagLinC hc x : ℓ²(ℕ, ℂ)) : ℕ → ℂ) n = c n * x n := by sorry
