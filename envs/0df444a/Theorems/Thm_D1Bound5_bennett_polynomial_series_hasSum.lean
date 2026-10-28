-- Prove2me | Theorems.Thm_D1Bound5_bennett_polynomial_series_hasSum
-- name    : D1Bound5.bennett_polynomial_series_hasSum
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:29:34.59374+00:00
-- url     : https://prove2.me/theorems/5a777a31-76a9-4c0b-b38d-6db417dd013d
-- title:
--   Bennett polynomial series has Sum
-- statement:
--   Multiplication by a polynomial commutes with analytic summation of a power series. Absolute summability makes the Cauchy-product step explicit.
-- source:
--   D1Bound5/BennettResidualEvaluation.lean, lines 11-43, SHA-256 d030bc1b298c007855437a873b058dcac35949cc3daa110cf555bdf87d4fd831. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.bennett_polynomial_series_hasSum (P : Polynomial ℂ) (B : PowerSeries ℂ)
    (x b : ℂ)
    (hB : HasSum (fun r : ℕ => PowerSeries.coeff r B * x ^ r) b)
    (hBnorm : Summable (fun r : ℕ => ‖PowerSeries.coeff r B * x ^ r‖)) :
    HasSum (fun r : ℕ => PowerSeries.coeff r ((P : PowerSeries ℂ) * B) * x ^ r)
      (P.eval x * b) := by sorry



section Nodes

variable {I : Type*} [Fintype I] [DecidableEq I]







end Nodes

end D1Bound5
end
