-- Prove2me | Theorems.Thm_BookProof_GaussCoreQuadBounds_coreD_sq_mul
-- name    : BookProof.GaussCoreQuadBounds.coreD_sq_mul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T11:49:09.112984+00:00
-- url     : https://prove2.me/theorems/20d74d4f-c929-42cb-88d9-18d46b155d7c
-- title:
--   (j : Fin D) (f p : MvPolynomial (Fin D) ℂ) : coreD j (coreD j (f * p)) = pderiv j (pderiv j f) * p + (2 : ℂ) • (pderiv j f * coreD j p) + f * coreD j (coreD j p)
-- statement:
--   Lean 4 theorem `BookProof.GaussCoreQuadBounds.coreD_sq_mul` (module `BookProof.GaussCoreQuadBounds`), source chapter `BookProof/ChapterGaussCoreQuadBounds.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterGaussCoreQuadBounds.lean

-- Generated from ChapterGaussCoreQuadBounds.lean — theorem BookProof.GaussCoreQuadBounds.coreD_sq_mul
import Mathlib
import Definitions.Def_ChapterGaussCoreQuadBounds
open BookProof.GaussCoreQuadBounds








open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.FarisLavine

noncomputable section

variable {D : ℕ}

theorem BookProof.GaussCoreQuadBounds.coreD_sq_mul (j : Fin D) (f p : MvPolynomial (Fin D) ℂ) :
    coreD j (coreD j (f * p))
      = pderiv j (pderiv j f) * p + (2 : ℂ) • (pderiv j f * coreD j p)
        + f * coreD j (coreD j p) := by sorry
