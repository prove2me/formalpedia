-- Prove2me | Theorems.Thm_BookProof_QuadraticRotation_quadPoly_apply_prime
-- name    : BookProof.QuadraticRotation.quadPoly_apply_prime
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-04T02:00:09.847069+00:00
-- url     : https://prove2.me/theorems/4dd64c03-c85a-42d7-9b2a-9ac811080e06
-- title:
--   The Lean 4 theorem `quadPoly_apply'` in the `ChapterQuadraticRotationEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `quadPoly_apply'` in the `ChapterQuadraticRotationEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQuadraticRotationEsa.lean

-- Generated from ChapterQuadraticRotationEsa.lean — theorem BookProof.QuadraticRotation.quadPoly_apply'
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterQuadraticRotationEsa
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterShiftedQuadraticEsa
import Definitions.Def_ChapterShiftedQuadraticMatrixEsa
open BookProof.HyperbolicQuadratic
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.QuadraticRotation



open MeasureTheory MvPolynomial Matrix
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HyperbolicQuadratic

noncomputable section

variable {d : ℕ}

theorem BookProof.QuadraticRotation.quadPoly_apply_prime (c : Fin d → ℝ) (p : MvPolynomial (Fin d) ℂ) :
    quadPoly c p = ∑ i, ((c i : ℝ) : ℂ) •
      (momPoly i (momPoly i p) + (1/4 : ℂ) • (X i * (X i * p))) := by sorry
