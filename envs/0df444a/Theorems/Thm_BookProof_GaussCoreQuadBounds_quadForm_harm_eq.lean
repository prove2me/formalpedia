-- Prove2me | Theorems.Thm_BookProof_GaussCoreQuadBounds_quadForm_harm_eq
-- name    : BookProof.GaussCoreQuadBounds.quadForm_harm_eq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T12:01:04.018976+00:00
-- url     : https://prove2.me/theorems/15edb866-b518-4cf1-adac-89f80ee4e268
-- title:
--   (p : MvPolynomial (Fin D) ℂ) : quadForm harmCore ⟨pgLp p, pgLp_mem_core p⟩ = ∑ j : Fin D, (‖pgLp (coreD j p)‖ ^ 2 + ‖pgLp (X j * p)‖ ^ 2 / 4)
-- statement:
--   Lean 4 theorem `BookProof.GaussCoreQuadBounds.quadForm_harm_eq` (module `BookProof.GaussCoreQuadBounds`), source chapter `BookProof/ChapterGaussCoreQuadBounds.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterGaussCoreQuadBounds.lean

-- Generated from ChapterGaussCoreQuadBounds.lean — theorem BookProof.GaussCoreQuadBounds.quadForm_harm_eq
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

theorem BookProof.GaussCoreQuadBounds.quadForm_harm_eq (p : MvPolynomial (Fin D) ℂ) :
    quadForm harmCore ⟨pgLp p, pgLp_mem_core p⟩
      = ∑ j : Fin D, (‖pgLp (coreD j p)‖ ^ 2 + ‖pgLp (X j * p)‖ ^ 2 / 4) := by sorry
