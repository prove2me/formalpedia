-- Prove2me | Theorems.Thm_BookProof_GaussCoreQuadBounds_gaussInt_self
-- name    : BookProof.GaussCoreQuadBounds.gaussInt_self
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T11:45:40.092643+00:00
-- url     : https://prove2.me/theorems/83aefef2-98f6-4e59-8c3d-7be9d651de84
-- title:
--   (q : MvPolynomial (Fin D) ℂ) : gaussInt (cpoly q * q) = ((‖pgLp q‖ ^ 2 : ℝ) : ℂ)
-- statement:
--   Lean 4 theorem `BookProof.GaussCoreQuadBounds.gaussInt_self` (module `BookProof.GaussCoreQuadBounds`), source chapter `BookProof/ChapterGaussCoreQuadBounds.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterGaussCoreQuadBounds.lean

-- Generated from ChapterGaussCoreQuadBounds.lean — theorem BookProof.GaussCoreQuadBounds.gaussInt_self
import Mathlib
import Definitions.Def_ChapterGaussCoreQuadBounds
open BookProof.GaussCoreQuadBounds








open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.FarisLavine

noncomputable section

variable {D : ℕ}

theorem BookProof.GaussCoreQuadBounds.gaussInt_self (q : MvPolynomial (Fin D) ℂ) :
    gaussInt (cpoly q * q) = ((‖pgLp q‖ ^ 2 : ℝ) : ℂ) := by sorry
