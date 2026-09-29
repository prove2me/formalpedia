-- Prove2me | Theorems.Thm_BookProof_GaussCoreQuadBounds_sqrt_dim_mul_norm_le_shiftNorm
-- name    : BookProof.GaussCoreQuadBounds.sqrt_dim_mul_norm_le_shiftNorm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T12:16:36.548914+00:00
-- url     : https://prove2.me/theorems/8b5da0ee-0d11-4872-9fc3-586eecc4878e
-- title:
--   (p : MvPolynomial (Fin D) ℂ) : Real.sqrt ((D : ℝ) / 2) * ‖pgLp p‖ ≤ shiftNorm p
-- statement:
--   Lean 4 theorem `BookProof.GaussCoreQuadBounds.sqrt_dim_mul_norm_le_shiftNorm` (module `BookProof.GaussCoreQuadBounds`), source chapter `BookProof/ChapterGaussCoreQuadBounds.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterGaussCoreQuadBounds.lean

-- Generated from ChapterGaussCoreQuadBounds.lean — theorem BookProof.GaussCoreQuadBounds.sqrt_dim_mul_norm_le_shiftNorm
import Mathlib
import Definitions.Def_ChapterGaussCoreQuadBounds
open BookProof.GaussCoreQuadBounds








open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.FarisLavine

noncomputable section

variable {D : ℕ}

theorem BookProof.GaussCoreQuadBounds.sqrt_dim_mul_norm_le_shiftNorm (p : MvPolynomial (Fin D) ℂ) :
    Real.sqrt ((D : ℝ) / 2) * ‖pgLp p‖ ≤ shiftNorm p := by sorry
