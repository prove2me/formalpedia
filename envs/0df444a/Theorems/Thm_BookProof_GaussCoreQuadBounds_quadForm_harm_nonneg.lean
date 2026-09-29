-- Prove2me | Theorems.Thm_BookProof_GaussCoreQuadBounds_quadForm_harm_nonneg
-- name    : BookProof.GaussCoreQuadBounds.quadForm_harm_nonneg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T12:00:55.273336+00:00
-- url     : https://prove2.me/theorems/381898e1-2740-4970-a72a-a75facaa50b7
-- title:
--   (p : MvPolynomial (Fin D) ℂ) : 0 ≤ quadForm harmCore ⟨pgLp p, pgLp_mem_core p⟩
-- statement:
--   Lean 4 theorem `BookProof.GaussCoreQuadBounds.quadForm_harm_nonneg` (module `BookProof.GaussCoreQuadBounds`), source chapter `BookProof/ChapterGaussCoreQuadBounds.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterGaussCoreQuadBounds.lean

-- Generated from ChapterGaussCoreQuadBounds.lean — theorem BookProof.GaussCoreQuadBounds.quadForm_harm_nonneg
import Mathlib
import Definitions.Def_ChapterGaussCoreQuadBounds
import Definitions.Def_ChapterQgHermiteOscillatorEsa
open BookProof.GaussCoreQuadBounds








open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.FarisLavine
open BookProof.QgHermiteOscillator

noncomputable section

variable {D : ℕ}

theorem BookProof.GaussCoreQuadBounds.quadForm_harm_nonneg (p : MvPolynomial (Fin D) ℂ) :
    0 ≤ quadForm harmCore ⟨pgLp p, pgLp_mem_core p⟩ := by sorry
