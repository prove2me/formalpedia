-- Prove2me | Theorems.Thm_BookProof_GaussCoreQuadBounds_norm_pgLp_le_shiftNorm
-- name    : BookProof.GaussCoreQuadBounds.norm_pgLp_le_shiftNorm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T12:07:02.182985+00:00
-- url     : https://prove2.me/theorems/66f6a600-0eda-4179-81a6-263ea0231f9a
-- title:
--   (p : MvPolynomial (Fin D) ℂ) : ‖pgLp p‖ ≤ shiftNorm p
-- statement:
--   Lean 4 theorem `BookProof.GaussCoreQuadBounds.norm_pgLp_le_shiftNorm` (module `BookProof.GaussCoreQuadBounds`), source chapter `BookProof/ChapterGaussCoreQuadBounds.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterGaussCoreQuadBounds.lean

-- Generated from ChapterGaussCoreQuadBounds.lean — theorem BookProof.GaussCoreQuadBounds.norm_pgLp_le_shiftNorm
import Mathlib
import Definitions.Def_ChapterGaussCoreQuadBounds
open BookProof.GaussCoreQuadBounds








open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.FarisLavine

noncomputable section

variable {D : ℕ}

theorem BookProof.GaussCoreQuadBounds.norm_pgLp_le_shiftNorm (p : MvPolynomial (Fin D) ℂ) : ‖pgLp p‖ ≤ shiftNorm p := by sorry
