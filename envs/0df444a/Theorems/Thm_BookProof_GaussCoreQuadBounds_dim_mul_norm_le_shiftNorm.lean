-- Prove2me | Theorems.Thm_BookProof_GaussCoreQuadBounds_dim_mul_norm_le_shiftNorm
-- name    : BookProof.GaussCoreQuadBounds.dim_mul_norm_le_shiftNorm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T12:06:56.576818+00:00
-- url     : https://prove2.me/theorems/7ce6acb3-00e5-4e66-ac06-e923a6eb526c
-- title:
--   (p : MvPolynomial (Fin D) ℂ) : ((D : ℝ) / 2 + 1) * ‖pgLp p‖ ≤ shiftNorm p
-- statement:
--   Lean 4 theorem `BookProof.GaussCoreQuadBounds.dim_mul_norm_le_shiftNorm` (module `BookProof.GaussCoreQuadBounds`), source chapter `BookProof/ChapterGaussCoreQuadBounds.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterGaussCoreQuadBounds.lean

-- Generated from ChapterGaussCoreQuadBounds.lean — theorem BookProof.GaussCoreQuadBounds.dim_mul_norm_le_shiftNorm
import Mathlib
import Definitions.Def_ChapterGaussCoreQuadBounds
open BookProof.GaussCoreQuadBounds








open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.FarisLavine

noncomputable section

variable {D : ℕ}

theorem BookProof.GaussCoreQuadBounds.dim_mul_norm_le_shiftNorm (p : MvPolynomial (Fin D) ℂ) :
    ((D : ℝ) / 2 + 1) * ‖pgLp p‖ ≤ shiftNorm p := by sorry
