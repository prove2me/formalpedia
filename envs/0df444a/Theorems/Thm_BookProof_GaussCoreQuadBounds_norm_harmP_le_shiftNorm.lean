-- Prove2me | Theorems.Thm_BookProof_GaussCoreQuadBounds_norm_harmP_le_shiftNorm
-- name    : BookProof.GaussCoreQuadBounds.norm_harmP_le_shiftNorm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T12:07:31.825976+00:00
-- url     : https://prove2.me/theorems/fabdd2b2-27df-428e-acf6-fd7da0b9bc77
-- title:
--   (p : MvPolynomial (Fin D) ℂ) : ‖pgLp (harmP p)‖ ≤ shiftNorm p
-- statement:
--   Lean 4 theorem `BookProof.GaussCoreQuadBounds.norm_harmP_le_shiftNorm` (module `BookProof.GaussCoreQuadBounds`), source chapter `BookProof/ChapterGaussCoreQuadBounds.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterGaussCoreQuadBounds.lean

-- Generated from ChapterGaussCoreQuadBounds.lean — theorem BookProof.GaussCoreQuadBounds.norm_harmP_le_shiftNorm
import Mathlib
import Definitions.Def_ChapterGaussCoreQuadBounds
open BookProof.GaussCoreQuadBounds








open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.FarisLavine

noncomputable section

variable {D : ℕ}

theorem BookProof.GaussCoreQuadBounds.norm_harmP_le_shiftNorm (p : MvPolynomial (Fin D) ℂ) :
    ‖pgLp (harmP p)‖ ≤ shiftNorm p := by sorry
