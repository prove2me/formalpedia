-- Prove2me | Theorems.Thm_BookProof_GaussCoreQuadBounds_coreD_comm
-- name    : BookProof.GaussCoreQuadBounds.coreD_comm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T11:38:46.316986+00:00
-- url     : https://prove2.me/theorems/fabb8e1f-c14f-48c7-a623-95dd0aacece8
-- title:
--   (j k : Fin D) (p : MvPolynomial (Fin D) ℂ) : coreD j (coreD k p) = coreD k (coreD j p)
-- statement:
--   Lean 4 theorem `BookProof.GaussCoreQuadBounds.coreD_comm` (module `BookProof.GaussCoreQuadBounds`), source chapter `BookProof/ChapterGaussCoreQuadBounds.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterGaussCoreQuadBounds.lean

-- Generated from ChapterGaussCoreQuadBounds.lean — theorem BookProof.GaussCoreQuadBounds.coreD_comm
import Mathlib
import Definitions.Def_ChapterGaussCoreQuadBounds
open BookProof.GaussCoreQuadBounds








open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.FarisLavine

noncomputable section

variable {D : ℕ}

theorem BookProof.GaussCoreQuadBounds.coreD_comm (j k : Fin D) (p : MvPolynomial (Fin D) ℂ) :
    coreD j (coreD k p) = coreD k (coreD j p) := by sorry
