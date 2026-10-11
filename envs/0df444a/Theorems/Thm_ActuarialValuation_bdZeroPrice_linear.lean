-- Prove2me | Theorems.Thm_ActuarialValuation_bdZeroPrice_linear
-- name    : ActuarialValuation.bdZeroPrice_linear
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T11:32:20.004252+00:00
-- url     : https://prove2.me/theorems/14358944-cf40-494d-89c4-dac3af895fa8
-- title:
--   Deterministic zero-coupon bonds and forward discounts: bdZeroPrice_linear
-- statement:
--   Time-zero bond valuation is additive in face value at the same maturity.
--
--   Mathematical relation:
--
--   $$
--   bdZeroPrice\_linear
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 2.12–2.13 and 20.13, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.jstor.org/stable/2951677. The proposed model is rooted in Promislow chapter 2.12–2.13 and 20.13. The target Lean identity is an original derivation, not a verbatim published result. Published source page 367 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_bdZeroPrice

namespace ActuarialValuation

theorem bdZeroPrice_linear (D : ℕ → ℝ) (t : ℕ) (x y : ℝ) : bdZeroPrice D (x+y) t = bdZeroPrice D x t + bdZeroPrice D y t := by sorry

end ActuarialValuation
