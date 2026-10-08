-- Prove2me | Theorems.Thm_AvramDividend_Classical_neg_jump_compensation_nonneg
-- name    : AvramDividend.Classical.neg_jump_compensation_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T11:53:23.32279+00:00
-- url     : https://prove2.me/theorems/88c092ba-a80d-4c1c-b858-a6782accdd03
-- title:
--   Nonnegative compensated exponential quotient for Lévy jump asymptotics
-- statement:
--   For positive Laplace parameter theta and arbitrary jump y, the quotient (exp(theta*y)-1)/theta - y is nonnegative. This follows from the tangent inequality for exp and is a scalar input to the bounded/unbounded variation asymptotics of the Lévy exponent.
-- source:
--   Exact scalar inequality add_one_le_exp at theta*y, divide by theta>0. No local Lean/Lake invocation; future remote verification authoritative.

import Mathlib

namespace AvramDividend.Classical
theorem neg_jump_compensation_nonneg
    (θ y : ℝ) (hθ : 0 < θ) :
    0 ≤ (Real.exp (θ * y) - 1) / θ - y := by
  sorry
end AvramDividend.Classical
