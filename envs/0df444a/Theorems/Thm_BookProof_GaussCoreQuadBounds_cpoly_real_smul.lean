-- Prove2me | Theorems.Thm_BookProof_GaussCoreQuadBounds_cpoly_real_smul
-- name    : BookProof.GaussCoreQuadBounds.cpoly_real_smul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T11:39:26.466983+00:00
-- url     : https://prove2.me/theorems/6875b219-d41d-4b74-968d-d5aaf54bdfd7
-- title:
--   (c : ℝ) (q : MvPolynomial (Fin D) ℂ) : cpoly (((c : ℝ) : ℂ) • q) = ((c : ℝ) : ℂ) • cpoly q
-- statement:
--   Lean 4 theorem `BookProof.GaussCoreQuadBounds.cpoly_real_smul` (module `BookProof.GaussCoreQuadBounds`), source chapter `BookProof/ChapterGaussCoreQuadBounds.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterGaussCoreQuadBounds.lean

-- Generated from ChapterGaussCoreQuadBounds.lean — theorem BookProof.GaussCoreQuadBounds.cpoly_real_smul
import Mathlib
import Definitions.Def_ChapterGaussCoreQuadBounds
open BookProof.GaussCoreQuadBounds








open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.FarisLavine

noncomputable section

variable {D : ℕ}

theorem BookProof.GaussCoreQuadBounds.cpoly_real_smul (c : ℝ) (q : MvPolynomial (Fin D) ℂ) :
    cpoly (((c : ℝ) : ℂ) • q) = ((c : ℝ) : ℂ) • cpoly q := by sorry
