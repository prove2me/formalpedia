-- Prove2me | Theorems.Thm_BookProof_GaussCoreQuadBounds_gaussInt_coreD_sq_pair
-- name    : BookProof.GaussCoreQuadBounds.gaussInt_coreD_sq_pair
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T11:50:50.857899+00:00
-- url     : https://prove2.me/theorems/ba9a6963-cc8f-401d-bfdd-d8563af23f5b
-- title:
--   (j k : Fin D) (p : MvPolynomial (Fin D) ℂ) : gaussInt (cpoly (coreD j (coreD j p)) * coreD k (coreD k p)) = ((‖pgLp (coreD k (coreD j p))‖ ^ 2 : ℝ) : ℂ)
-- statement:
--   Lean 4 theorem `BookProof.GaussCoreQuadBounds.gaussInt_coreD_sq_pair` (module `BookProof.GaussCoreQuadBounds`), source chapter `BookProof/ChapterGaussCoreQuadBounds.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterGaussCoreQuadBounds.lean

-- Generated from ChapterGaussCoreQuadBounds.lean — theorem BookProof.GaussCoreQuadBounds.gaussInt_coreD_sq_pair
import Mathlib
import Definitions.Def_ChapterGaussCoreQuadBounds
open BookProof.GaussCoreQuadBounds








open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.FarisLavine

noncomputable section

variable {D : ℕ}

theorem BookProof.GaussCoreQuadBounds.gaussInt_coreD_sq_pair (j k : Fin D) (p : MvPolynomial (Fin D) ℂ) :
    gaussInt (cpoly (coreD j (coreD j p)) * coreD k (coreD k p))
      = ((‖pgLp (coreD k (coreD j p))‖ ^ 2 : ℝ) : ℂ) := by sorry
