-- Prove2me | Theorems.Thm_BookProof_GaussCoreQuadBounds_re_inner_symm
-- name    : BookProof.GaussCoreQuadBounds.re_inner_symm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T11:46:16.35677+00:00
-- url     : https://prove2.me/theorems/8f00abe3-c0b0-4448-8103-dfcc8bdde786
-- title:
--   (a b : L2d D) : (inner ℂ a b : ℂ).re = (inner ℂ b a : ℂ).re
-- statement:
--   Lean 4 theorem `BookProof.GaussCoreQuadBounds.re_inner_symm` (module `BookProof.GaussCoreQuadBounds`), source chapter `BookProof/ChapterGaussCoreQuadBounds.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterGaussCoreQuadBounds.lean

-- Generated from ChapterGaussCoreQuadBounds.lean — theorem BookProof.GaussCoreQuadBounds.re_inner_symm
import Mathlib
import Definitions.Def_ChapterGaussCoreQuadBounds
open BookProof.GaussCoreQuadBounds








open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.FarisLavine

noncomputable section

variable {D : ℕ}

theorem BookProof.GaussCoreQuadBounds.re_inner_symm (a b : L2d D) :
    (inner ℂ a b : ℂ).re = (inner ℂ b a : ℂ).re := by sorry
