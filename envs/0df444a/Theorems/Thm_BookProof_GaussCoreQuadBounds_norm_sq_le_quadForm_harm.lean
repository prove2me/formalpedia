-- Prove2me | Theorems.Thm_BookProof_GaussCoreQuadBounds_norm_sq_le_quadForm_harm
-- name    : BookProof.GaussCoreQuadBounds.norm_sq_le_quadForm_harm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T12:02:54.206755+00:00
-- url     : https://prove2.me/theorems/d91dedb0-5058-4229-a885-ed0f3c374ec1
-- title:
--   (p : MvPolynomial (Fin D) ℂ) : ((D : ℝ) / 2) * ‖pgLp p‖ ^ 2 ≤ quadForm harmCore ⟨pgLp p, pgLp_mem_core p⟩
-- statement:
--   Lean 4 theorem `BookProof.GaussCoreQuadBounds.norm_sq_le_quadForm_harm` (module `BookProof.GaussCoreQuadBounds`), source chapter `BookProof/ChapterGaussCoreQuadBounds.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterGaussCoreQuadBounds.lean

-- Generated from ChapterGaussCoreQuadBounds.lean — theorem BookProof.GaussCoreQuadBounds.norm_sq_le_quadForm_harm
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

theorem BookProof.GaussCoreQuadBounds.norm_sq_le_quadForm_harm (p : MvPolynomial (Fin D) ℂ) :
    ((D : ℝ) / 2) * ‖pgLp p‖ ^ 2 ≤ quadForm harmCore ⟨pgLp p, pgLp_mem_core p⟩ := by sorry
