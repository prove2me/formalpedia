-- Prove2me | Theorems.Thm_D1Bound5_bennett_coeff_mul_trunc
-- name    : D1Bound5.bennett_coeff_mul_trunc
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:35:29.953418+00:00
-- url     : https://prove2.me/theorems/b6d83ee2-60e3-4f10-93cf-ed2e71f0e7f7
-- title:
--   Bennett coeff mul trunc
-- statement:
--   Truncating a multiplier preserves every coefficient below the truncation order, even when the other factor is an infinite series.
-- source:
--   D1Bound5/BennettResidualCancellation.lean, lines 106-117, SHA-256 0e8f4d1dac16aef29c7622ad8fa6e48d05646e38a9ebaf133da673991996797d. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic.Ring

section
open Finset

namespace D1Bound5

variable {F : Type*} [Field F] [CharZero F]



section Nodes

variable {I : Type*} [Fintype I] [DecidableEq I]




theorem _root_.D1Bound5.bennett_coeff_mul_trunc (P θ : PowerSeries F) (D r : ℕ) (hr : r < D) :
    PowerSeries.coeff r (P * (PowerSeries.trunc D θ : PowerSeries F)) =
      PowerSeries.coeff r (P * θ) := by sorry







end Nodes

end D1Bound5
end
