-- Prove2me | Theorems.Thm_D1Bound5_bennett_rescaled_binomial_hasSum
-- name    : D1Bound5.bennett_rescaled_binomial_hasSum
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:34:11.079863+00:00
-- url     : https://prove2.me/theorems/26718e07-a33c-4341-916f-40fed7d2c8c0
-- title:
--   Bennett rescaled binomial has Sum
-- statement:
--   The rescaled formal binomial series evaluates to the principal complex power in the unit disk, with absolute summability.
-- source:
--   D1Bound5/BennettResidualEvaluation.lean, lines 45-72, SHA-256 d030bc1b298c007855437a873b058dcac35949cc3daa110cf555bdf87d4fd831. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic.Ring

section
open Finset

namespace D1Bound5




theorem _root_.D1Bound5.bennett_rescaled_binomial_hasSum (a ν x : ℂ) (hx : ‖a * x‖ < 1) :
    HasSum (fun r : ℕ =>
      PowerSeries.coeff r (PowerSeries.rescale a (PowerSeries.binomialSeries ℂ ν)) *
        x ^ r) ((1 + a * x) ^ ν) ∧
    Summable (fun r : ℕ =>
      ‖PowerSeries.coeff r
        (PowerSeries.rescale a (PowerSeries.binomialSeries ℂ ν)) * x ^ r‖) := by sorry

section Nodes

variable {I : Type*} [Fintype I] [DecidableEq I]







end Nodes

end D1Bound5
end
