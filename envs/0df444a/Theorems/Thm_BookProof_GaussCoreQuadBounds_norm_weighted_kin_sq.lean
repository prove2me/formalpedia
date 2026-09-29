-- Prove2me | Theorems.Thm_BookProof_GaussCoreQuadBounds_norm_weighted_kin_sq
-- name    : BookProof.GaussCoreQuadBounds.norm_weighted_kin_sq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T12:02:05.617665+00:00
-- url     : https://prove2.me/theorems/a71e250b-fff5-4931-a248-55617a88bd69
-- title:
--   (c : Fin D → ℝ) (p : MvPolynomial (Fin D) ℂ) : ‖pgLp (∑ j : Fin D, ((c j : ℝ) : ℂ) • coreD j (coreD j p))‖ ^ 2 = ∑ j : Fin D, ∑ k : Fin D, c j * c k * ‖pgLp (coreD k...
-- statement:
--   Lean 4 theorem `BookProof.GaussCoreQuadBounds.norm_weighted_kin_sq` (module `BookProof.GaussCoreQuadBounds`), source chapter `BookProof/ChapterGaussCoreQuadBounds.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterGaussCoreQuadBounds.lean

-- Generated from ChapterGaussCoreQuadBounds.lean — theorem BookProof.GaussCoreQuadBounds.norm_weighted_kin_sq
import Mathlib
import Definitions.Def_ChapterGaussCoreQuadBounds
open BookProof.GaussCoreQuadBounds








open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.FarisLavine

noncomputable section

variable {D : ℕ}

theorem BookProof.GaussCoreQuadBounds.norm_weighted_kin_sq (c : Fin D → ℝ) (p : MvPolynomial (Fin D) ℂ) :
    ‖pgLp (∑ j : Fin D, ((c j : ℝ) : ℂ) • coreD j (coreD j p))‖ ^ 2
      = ∑ j : Fin D, ∑ k : Fin D, c j * c k * ‖pgLp (coreD k (coreD j p))‖ ^ 2 := by sorry
