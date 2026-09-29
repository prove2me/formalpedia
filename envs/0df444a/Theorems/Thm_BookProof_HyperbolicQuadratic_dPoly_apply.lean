-- Prove2me | Theorems.Thm_BookProof_HyperbolicQuadratic_dPoly_apply
-- name    : BookProof.HyperbolicQuadratic.dPoly_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T06:58:56.553393+00:00
-- url     : https://prove2.me/theorems/de155d6a-713f-4efb-9400-884448699307
-- title:
--   The Lean 4 theorem `dPoly_apply` in the `ChapterHyperbolicQuadraticEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `dPoly_apply` in the `ChapterHyperbolicQuadraticEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHyperbolicQuadraticEsa.lean

-- Generated from ChapterHyperbolicQuadraticEsa.lean — theorem BookProof.HyperbolicQuadratic.dPoly_apply
import Mathlib
import Definitions.Def_ChapterHyperbolicQuadraticEsa
open BookProof.HyperbolicQuadratic



open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2

noncomputable section

variable {d : ℕ}

theorem BookProof.HyperbolicQuadratic.dPoly_apply (i : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    dPoly i p = pderiv i p - (1/2 : ℂ) • (X i * p) := by sorry
