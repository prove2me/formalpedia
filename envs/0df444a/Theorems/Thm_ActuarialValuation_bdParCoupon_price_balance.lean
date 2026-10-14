-- Prove2me | Theorems.Thm_ActuarialValuation_bdParCoupon_price_balance
-- name    : ActuarialValuation.bdParCoupon_price_balance
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:40:24.320019+00:00
-- url     : https://prove2.me/theorems/5a98e68c-569e-4ad8-9fe1-b09337c3f48b
-- title:
--   Coupon-bond cashflows duration and flat yield: bdParCoupon_price_balance
-- statement:
--   The par coupon rate is exactly the coupon level that prices a unit-redemption bond at par, provided its coupon annuity is nonzero.
--
--   Mathematical relation:
--
--   $$
--   bdParCoupon\_price\_balance
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 2.12–2.13 and 20.13, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.jstor.org/stable/2951677. The proposed model is rooted in Promislow chapter 2.12–2.13 and 20.13. The target Lean identity is an original derivation, not a verbatim published result. Published source page 367 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_bdParCoupon

namespace ActuarialValuation

theorem bdParCoupon_price_balance (D : ℕ → ℝ) (n : ℕ) (ha : (∑ k∈Finset.range n, D (k+1)) ≠ 0) : bdParCoupon D n * (∑ k∈Finset.range n, D (k+1)) + D n = 1 := by sorry

end ActuarialValuation
