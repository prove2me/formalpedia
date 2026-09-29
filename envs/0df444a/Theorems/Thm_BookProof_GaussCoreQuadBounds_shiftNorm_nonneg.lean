-- Prove2me | Theorems.Thm_BookProof_GaussCoreQuadBounds_shiftNorm_nonneg
-- name    : BookProof.GaussCoreQuadBounds.shiftNorm_nonneg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T11:46:31.766976+00:00
-- url     : https://prove2.me/theorems/5dbc4c81-081c-4601-ad93-e595010c9bb6
-- title:
--   (p : MvPolynomial (Fin D) ℂ) : 0 ≤ shiftNorm p
-- statement:
--   Lean 4 theorem `BookProof.GaussCoreQuadBounds.shiftNorm_nonneg` (module `BookProof.GaussCoreQuadBounds`), source chapter `BookProof/ChapterGaussCoreQuadBounds.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterGaussCoreQuadBounds.lean

-- Generated from ChapterGaussCoreQuadBounds.lean — theorem BookProof.GaussCoreQuadBounds.shiftNorm_nonneg
import Mathlib
import Definitions.Def_ChapterGaussCoreQuadBounds
open BookProof.GaussCoreQuadBounds








open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.FarisLavine

noncomputable section

variable {D : ℕ}

theorem BookProof.GaussCoreQuadBounds.shiftNorm_nonneg (p : MvPolynomial (Fin D) ℂ) : 0 ≤ shiftNorm p := by sorry
