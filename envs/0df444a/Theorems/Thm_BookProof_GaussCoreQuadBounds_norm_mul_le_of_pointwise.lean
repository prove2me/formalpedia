-- Prove2me | Theorems.Thm_BookProof_GaussCoreQuadBounds_norm_mul_le_of_pointwise
-- name    : BookProof.GaussCoreQuadBounds.norm_mul_le_of_pointwise
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T12:01:39.346983+00:00
-- url     : https://prove2.me/theorems/b61488c3-4907-4f09-ac19-65203debb743
-- title:
--   {f g : MvPolynomial (Fin D) ℂ} {lam : ℝ} (hlam : 0 ≤ lam) (h : ∀ x : Vd D, ‖MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) f‖ ≤ lam * ‖MvPolynomial.eval (fun i => ((x i : ℝ)...
-- statement:
--   Lean 4 theorem `BookProof.GaussCoreQuadBounds.norm_mul_le_of_pointwise` (module `BookProof.GaussCoreQuadBounds`), source chapter `BookProof/ChapterGaussCoreQuadBounds.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterGaussCoreQuadBounds.lean

-- Generated from ChapterGaussCoreQuadBounds.lean — theorem BookProof.GaussCoreQuadBounds.norm_mul_le_of_pointwise
import Mathlib
import Definitions.Def_ChapterGaussCoreQuadBounds
open BookProof.GaussCoreQuadBounds








open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.FarisLavine

noncomputable section

variable {D : ℕ}

theorem BookProof.GaussCoreQuadBounds.norm_mul_le_of_pointwise {f g : MvPolynomial (Fin D) ℂ} {lam : ℝ} (hlam : 0 ≤ lam)
    (h : ∀ x : Vd D, ‖MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) f‖
      ≤ lam * ‖MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) g‖)
    (p : MvPolynomial (Fin D) ℂ) :
    ‖pgLp (f * p)‖ ≤ lam * ‖pgLp (g * p)‖ := by sorry
