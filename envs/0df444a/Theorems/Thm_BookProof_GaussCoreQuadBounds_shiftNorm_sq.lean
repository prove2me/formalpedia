-- Prove2me | Theorems.Thm_BookProof_GaussCoreQuadBounds_shiftNorm_sq
-- name    : BookProof.GaussCoreQuadBounds.shiftNorm_sq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T12:03:20.957091+00:00
-- url     : https://prove2.me/theorems/2cb9499b-be63-40a7-919d-c6c3f6e7946c
-- title:
--   (p : MvPolynomial (Fin D) ℂ) : shiftNorm p ^ 2 = ‖pgLp (harmP p)‖ ^ 2 + 2 * quadForm harmCore ⟨pgLp p, pgLp_mem_core p⟩ + ‖pgLp p‖ ^ 2
-- statement:
--   Lean 4 theorem `BookProof.GaussCoreQuadBounds.shiftNorm_sq` (module `BookProof.GaussCoreQuadBounds`), source chapter `BookProof/ChapterGaussCoreQuadBounds.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterGaussCoreQuadBounds.lean

-- Generated from ChapterGaussCoreQuadBounds.lean — theorem BookProof.GaussCoreQuadBounds.shiftNorm_sq
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

theorem BookProof.GaussCoreQuadBounds.shiftNorm_sq (p : MvPolynomial (Fin D) ℂ) :
    shiftNorm p ^ 2 = ‖pgLp (harmP p)‖ ^ 2
      + 2 * quadForm harmCore ⟨pgLp p, pgLp_mem_core p⟩ + ‖pgLp p‖ ^ 2 := by sorry
