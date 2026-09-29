-- Prove2me | Theorems.Thm_BookProof_GaussCoreQuadBounds_gaussInt_re
-- name    : BookProof.GaussCoreQuadBounds.gaussInt_re
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T11:44:58.780162+00:00
-- url     : https://prove2.me/theorems/2ac6cdea-e91e-4f14-b950-63a2e43dc956
-- title:
--   (r : MvPolynomial (Fin D) ℂ) : (gaussInt r).re = ∫ x : Vd D, (MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) r).re * gaussWD x
-- statement:
--   Lean 4 theorem `BookProof.GaussCoreQuadBounds.gaussInt_re` (module `BookProof.GaussCoreQuadBounds`), source chapter `BookProof/ChapterGaussCoreQuadBounds.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterGaussCoreQuadBounds.lean

-- Generated from ChapterGaussCoreQuadBounds.lean — theorem BookProof.GaussCoreQuadBounds.gaussInt_re
import Mathlib
import Definitions.Def_ChapterGaussCoreQuadBounds
open BookProof.GaussCoreQuadBounds








open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.FarisLavine

noncomputable section

variable {D : ℕ}

theorem BookProof.GaussCoreQuadBounds.gaussInt_re (r : MvPolynomial (Fin D) ℂ) :
    (gaussInt r).re
      = ∫ x : Vd D, (MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) r).re * gaussWD x := by sorry
