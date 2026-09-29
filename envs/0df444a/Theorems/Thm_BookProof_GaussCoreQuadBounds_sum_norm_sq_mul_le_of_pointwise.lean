-- Prove2me | Theorems.Thm_BookProof_GaussCoreQuadBounds_sum_norm_sq_mul_le_of_pointwise
-- name    : BookProof.GaussCoreQuadBounds.sum_norm_sq_mul_le_of_pointwise
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T12:02:06.363599+00:00
-- url     : https://prove2.me/theorems/bdc89a73-36ac-45b7-8608-e629395eb47c
-- title:
--   {R : Type*} [Fintype R] {f : R → MvPolynomial (Fin D) ℂ} {g : R → MvPolynomial (Fin D) ℂ} {lam : ℝ} (h : ∀ x : Vd D, ∑ r : R, ‖MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (f...
-- statement:
--   Lean 4 theorem `BookProof.GaussCoreQuadBounds.sum_norm_sq_mul_le_of_pointwise` (module `BookProof.GaussCoreQuadBounds`), source chapter `BookProof/ChapterGaussCoreQuadBounds.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterGaussCoreQuadBounds.lean

-- Generated from ChapterGaussCoreQuadBounds.lean — theorem BookProof.GaussCoreQuadBounds.sum_norm_sq_mul_le_of_pointwise
import Mathlib
import Definitions.Def_ChapterGaussCoreQuadBounds
open BookProof.GaussCoreQuadBounds








open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.FarisLavine

noncomputable section

variable {D : ℕ}

theorem BookProof.GaussCoreQuadBounds.sum_norm_sq_mul_le_of_pointwise {R : Type*} [Fintype R]
    {f : R → MvPolynomial (Fin D) ℂ} {g : R → MvPolynomial (Fin D) ℂ} {lam : ℝ}
    (h : ∀ x : Vd D, ∑ r : R, ‖MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (f r)‖ ^ 2
      ≤ lam * ∑ r : R, ‖MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (g r)‖ ^ 2)
    (p : MvPolynomial (Fin D) ℂ) :
    ∑ r : R, ‖pgLp (f r * p)‖ ^ 2 ≤ lam * ∑ r : R, ‖pgLp (g r * p)‖ ^ 2 := by sorry
