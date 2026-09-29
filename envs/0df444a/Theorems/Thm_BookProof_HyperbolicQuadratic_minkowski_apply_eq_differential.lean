-- Prove2me | Theorems.Thm_BookProof_HyperbolicQuadratic_minkowski_apply_eq_differential
-- name    : BookProof.HyperbolicQuadratic.minkowski_apply_eq_differential
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T00:24:03.240295+00:00
-- url     : https://prove2.me/theorems/18b17e02-35b7-40a2-bbe4-154a2cfe1600
-- title:
--   The Lean 4 theorem `minkowski_apply_eq_differential` in the `ChapterHyperbolicQuadraticEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `minkowski_apply_eq_differential` in the `ChapterHyperbolicQuadraticEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHyperbolicQuadraticEsa.lean

-- Generated from ChapterHyperbolicQuadraticEsa.lean — theorem BookProof.HyperbolicQuadratic.minkowski_apply_eq_differential
import Mathlib
import Definitions.Def_ChapterHyperbolicQuadraticEsa
open BookProof.HyperbolicQuadratic



open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2

noncomputable section

theorem BookProof.HyperbolicQuadratic.minkowski_apply_eq_differential (n : ℕ) (p : MvPolynomial (Fin (1 + n)) ℂ)
    (x : Vd (1 + n)) :
    pgFun (quadPoly (minkowskiCoeff n) p) x
      = (-(deriv (fun t : ℝ => deriv (fun s : ℝ => pgFun p (sec 0 x s)) t) (x 0))
          + (((x 0 : ℝ) : ℂ) ^ 2 / 4) * pgFun p x)
        - ∑ k ∈ Finset.univ.erase (0 : Fin (1 + n)),
            (-(deriv (fun t : ℝ => deriv (fun s : ℝ => pgFun p (sec k x s)) t) (x k))
              + (((x k : ℝ) : ℂ) ^ 2 / 4) * pgFun p x) := by sorry
