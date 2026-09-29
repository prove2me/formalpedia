-- Prove2me | Theorems.Thm_BookProof_HyperbolicQuadratic_momPoly_sq_eq_dPoly
-- name    : BookProof.HyperbolicQuadratic.momPoly_sq_eq_dPoly
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T07:02:50.700693+00:00
-- url     : https://prove2.me/theorems/ffcbed5e-e83b-4268-b326-6dc29eaa443e
-- title:
--   The Lean 4 theorem `momPoly_sq_eq_dPoly` in the `ChapterHyperbolicQuadraticEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `momPoly_sq_eq_dPoly` in the `ChapterHyperbolicQuadraticEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHyperbolicQuadraticEsa.lean

-- Generated from ChapterHyperbolicQuadraticEsa.lean — theorem BookProof.HyperbolicQuadratic.momPoly_sq_eq_dPoly
import Mathlib
import Definitions.Def_ChapterHyperbolicQuadraticEsa
open BookProof.HyperbolicQuadratic



open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2

noncomputable section

variable {d : ℕ}

theorem BookProof.HyperbolicQuadratic.momPoly_sq_eq_dPoly (i : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    momPoly i (momPoly i p) = -(dPoly i (dPoly i p)) := by sorry
