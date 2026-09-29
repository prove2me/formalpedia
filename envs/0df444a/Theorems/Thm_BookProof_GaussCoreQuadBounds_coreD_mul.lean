-- Prove2me | Theorems.Thm_BookProof_GaussCoreQuadBounds_coreD_mul
-- name    : BookProof.GaussCoreQuadBounds.coreD_mul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T11:38:53.932983+00:00
-- url     : https://prove2.me/theorems/e2df96e1-9b14-4cd3-8767-890f223aacb5
-- title:
--   (j : Fin D) (f p : MvPolynomial (Fin D) ℂ) : coreD j (f * p) = pderiv j f * p + f * coreD j p
-- statement:
--   Lean 4 theorem `BookProof.GaussCoreQuadBounds.coreD_mul` (module `BookProof.GaussCoreQuadBounds`), source chapter `BookProof/ChapterGaussCoreQuadBounds.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterGaussCoreQuadBounds.lean

-- Generated from ChapterGaussCoreQuadBounds.lean — theorem BookProof.GaussCoreQuadBounds.coreD_mul
import Mathlib
import Definitions.Def_ChapterGaussCoreQuadBounds
open BookProof.GaussCoreQuadBounds








open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.FarisLavine

noncomputable section

variable {D : ℕ}

theorem BookProof.GaussCoreQuadBounds.coreD_mul (j : Fin D) (f p : MvPolynomial (Fin D) ℂ) :
    coreD j (f * p) = pderiv j f * p + f * coreD j p := by sorry
