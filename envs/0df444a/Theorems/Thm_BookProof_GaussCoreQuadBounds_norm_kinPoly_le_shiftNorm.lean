-- Prove2me | Theorems.Thm_BookProof_GaussCoreQuadBounds_norm_kinPoly_le_shiftNorm
-- name    : BookProof.GaussCoreQuadBounds.norm_kinPoly_le_shiftNorm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T13:21:34.144509+00:00
-- url     : https://prove2.me/theorems/3f728294-c1b3-4aaa-995f-3ef383b2b021
-- title:
--   (p : MvPolynomial (Fin D) ℂ) : ‖pgLp (kinPoly p)‖ ≤ 3 * shiftNorm p
-- statement:
--   Lean 4 theorem `BookProof.GaussCoreQuadBounds.norm_kinPoly_le_shiftNorm` (module `BookProof.GaussCoreQuadBounds`), source chapter `BookProof/ChapterGaussCoreQuadBounds.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterGaussCoreQuadBounds.lean

-- Generated from ChapterGaussCoreQuadBounds.lean — theorem BookProof.GaussCoreQuadBounds.norm_kinPoly_le_shiftNorm
import Mathlib
import Definitions.Def_ChapterGaussCoreQuadBounds
open BookProof.GaussCoreQuadBounds








open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.FarisLavine

noncomputable section

variable {D : ℕ}

theorem BookProof.GaussCoreQuadBounds.norm_kinPoly_le_shiftNorm (p : MvPolynomial (Fin D) ℂ) :
    ‖pgLp (kinPoly p)‖ ≤ 3 * shiftNorm p := by sorry
