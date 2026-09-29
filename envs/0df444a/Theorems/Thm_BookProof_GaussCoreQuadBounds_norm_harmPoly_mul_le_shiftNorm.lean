-- Prove2me | Theorems.Thm_BookProof_GaussCoreQuadBounds_norm_harmPoly_mul_le_shiftNorm
-- name    : BookProof.GaussCoreQuadBounds.norm_harmPoly_mul_le_shiftNorm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T13:15:56.363433+00:00
-- url     : https://prove2.me/theorems/899cbb7d-061f-4729-9f96-a1f0548be5bf
-- title:
--   (p : MvPolynomial (Fin D) ℂ) : ‖pgLp (harmPoly * p)‖ ≤ 2 * shiftNorm p
-- statement:
--   Lean 4 theorem `BookProof.GaussCoreQuadBounds.norm_harmPoly_mul_le_shiftNorm` (module `BookProof.GaussCoreQuadBounds`), source chapter `BookProof/ChapterGaussCoreQuadBounds.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterGaussCoreQuadBounds.lean

-- Generated from ChapterGaussCoreQuadBounds.lean — theorem BookProof.GaussCoreQuadBounds.norm_harmPoly_mul_le_shiftNorm
import Mathlib
import Definitions.Def_ChapterGaussCoreQuadBounds
open BookProof.GaussCoreQuadBounds








open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.FarisLavine

noncomputable section

variable {D : ℕ}

theorem BookProof.GaussCoreQuadBounds.norm_harmPoly_mul_le_shiftNorm (p : MvPolynomial (Fin D) ℂ) :
    ‖pgLp (harmPoly * p)‖ ≤ 2 * shiftNorm p := by sorry
