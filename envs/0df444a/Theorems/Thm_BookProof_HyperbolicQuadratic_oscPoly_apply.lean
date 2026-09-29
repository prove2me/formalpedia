-- Prove2me | Theorems.Thm_BookProof_HyperbolicQuadratic_oscPoly_apply
-- name    : BookProof.HyperbolicQuadratic.oscPoly_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T07:04:59.291655+00:00
-- url     : https://prove2.me/theorems/3b1d9637-de99-4ec7-b149-9d929f796ba6
-- title:
--   The Lean 4 theorem `oscPoly_apply` in the `ChapterHyperbolicQuadraticEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `oscPoly_apply` in the `ChapterHyperbolicQuadraticEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHyperbolicQuadraticEsa.lean

-- Generated from ChapterHyperbolicQuadraticEsa.lean — theorem BookProof.HyperbolicQuadratic.oscPoly_apply
import Mathlib
import Definitions.Def_ChapterHyperbolicQuadraticEsa
open BookProof.HyperbolicQuadratic



open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2

noncomputable section

variable {d : ℕ}

theorem BookProof.HyperbolicQuadratic.oscPoly_apply (i : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    oscPoly i p = X i * pderiv i p - pderiv i (pderiv i p) + (1/2 : ℂ) • p := by sorry
