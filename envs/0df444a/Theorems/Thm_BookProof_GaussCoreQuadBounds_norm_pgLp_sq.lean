-- Prove2me | Theorems.Thm_BookProof_GaussCoreQuadBounds_norm_pgLp_sq
-- name    : BookProof.GaussCoreQuadBounds.norm_pgLp_sq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T11:46:53.104356+00:00
-- url     : https://prove2.me/theorems/6fcb775e-8604-4a18-9034-b4184e4088a7
-- title:
--   (q : MvPolynomial (Fin D) ℂ) : ‖pgLp q‖ ^ 2 = (gaussInt (cpoly q * q)).re
-- statement:
--   Lean 4 theorem `BookProof.GaussCoreQuadBounds.norm_pgLp_sq` (module `BookProof.GaussCoreQuadBounds`), source chapter `BookProof/ChapterGaussCoreQuadBounds.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterGaussCoreQuadBounds.lean

-- Generated from ChapterGaussCoreQuadBounds.lean — theorem BookProof.GaussCoreQuadBounds.norm_pgLp_sq
import Mathlib
import Definitions.Def_ChapterGaussCoreQuadBounds
open BookProof.GaussCoreQuadBounds








open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.FarisLavine

noncomputable section

variable {D : ℕ}

theorem BookProof.GaussCoreQuadBounds.norm_pgLp_sq (q : MvPolynomial (Fin D) ℂ) :
    ‖pgLp q‖ ^ 2 = (gaussInt (cpoly q * q)).re := by sorry
