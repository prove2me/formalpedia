-- Prove2me | Theorems.Thm_BookProof_GaussCoreQuadBounds_coreD_X_comm
-- name    : BookProof.GaussCoreQuadBounds.coreD_X_comm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T12:01:06.837896+00:00
-- url     : https://prove2.me/theorems/fc35a7f4-04be-4e49-805b-4e98a9160b26
-- title:
--   (j : Fin D) (p : MvPolynomial (Fin D) ℂ) : coreD j (X j * p) - X j * coreD j p = p
-- statement:
--   Lean 4 theorem `BookProof.GaussCoreQuadBounds.coreD_X_comm` (module `BookProof.GaussCoreQuadBounds`), source chapter `BookProof/ChapterGaussCoreQuadBounds.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterGaussCoreQuadBounds.lean

-- Generated from ChapterGaussCoreQuadBounds.lean — theorem BookProof.GaussCoreQuadBounds.coreD_X_comm
import Mathlib
import Definitions.Def_ChapterGaussCoreQuadBounds
open BookProof.GaussCoreQuadBounds








open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.FarisLavine

noncomputable section

variable {D : ℕ}

theorem BookProof.GaussCoreQuadBounds.coreD_X_comm (j : Fin D) (p : MvPolynomial (Fin D) ℂ) :
    coreD j (X j * p) - X j * coreD j p = p := by sorry
