-- Prove2me | Theorems.Thm_BookProof_HyperbolicQuadratic_oscPoly_apply_eq_differential
-- name    : BookProof.HyperbolicQuadratic.oscPoly_apply_eq_differential
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T07:06:11.352728+00:00
-- url     : https://prove2.me/theorems/7ebb0cc6-b4c4-4bab-a431-f1b9b49dd3cf
-- title:
--   The Lean 4 theorem `oscPoly_apply_eq_differential` in the `ChapterHyperbolicQuadraticEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `oscPoly_apply_eq_differential` in the `ChapterHyperbolicQuadraticEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHyperbolicQuadraticEsa.lean

-- Generated from ChapterHyperbolicQuadraticEsa.lean — theorem BookProof.HyperbolicQuadratic.oscPoly_apply_eq_differential
import Mathlib
import Definitions.Def_ChapterHyperbolicQuadraticEsa
open BookProof.HyperbolicQuadratic



open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2

noncomputable section

variable {d : ℕ}

theorem BookProof.HyperbolicQuadratic.oscPoly_apply_eq_differential (i : Fin d) (p : MvPolynomial (Fin d) ℂ) (x : Vd d) :
    pgFun (oscPoly i p) x
      = -(deriv (fun t : ℝ => deriv (fun s : ℝ => pgFun p (sec i x s)) t) (x i))
        + (((x i : ℝ) : ℂ) ^ 2 / 4) * pgFun p x := by sorry
