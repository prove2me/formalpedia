-- Prove2me | Theorems.Thm_BookProof_GaussCoreQuadBounds_gaussInt_re_mono
-- name    : BookProof.GaussCoreQuadBounds.gaussInt_re_mono
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T11:48:52.612006+00:00
-- url     : https://prove2.me/theorems/f288cf41-1046-4457-8771-bacf2f3ec28e
-- title:
--   {r s : MvPolynomial (Fin D) ℂ} (h : ∀ x : Vd D, (MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) r).re ≤ (MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) s).re) : (gaussInt r).re ≤...
-- statement:
--   Lean 4 theorem `BookProof.GaussCoreQuadBounds.gaussInt_re_mono` (module `BookProof.GaussCoreQuadBounds`), source chapter `BookProof/ChapterGaussCoreQuadBounds.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterGaussCoreQuadBounds.lean

-- Generated from ChapterGaussCoreQuadBounds.lean — theorem BookProof.GaussCoreQuadBounds.gaussInt_re_mono
import Mathlib
import Definitions.Def_ChapterGaussCoreQuadBounds
open BookProof.GaussCoreQuadBounds








open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.FarisLavine

noncomputable section

variable {D : ℕ}

theorem BookProof.GaussCoreQuadBounds.gaussInt_re_mono {r s : MvPolynomial (Fin D) ℂ}
    (h : ∀ x : Vd D, (MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) r).re
      ≤ (MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) s).re) :
    (gaussInt r).re ≤ (gaussInt s).re := by sorry
