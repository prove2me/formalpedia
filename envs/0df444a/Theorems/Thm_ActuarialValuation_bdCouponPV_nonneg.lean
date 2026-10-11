-- Prove2me | Theorems.Thm_ActuarialValuation_bdCouponPV_nonneg
-- name    : ActuarialValuation.bdCouponPV_nonneg
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T11:39:07.045681+00:00
-- url     : https://prove2.me/theorems/f0cc5b0c-ed1e-4dc9-b4b1-87e3a7715b68
-- title:
--   Coupon-bond cashflows duration and flat yield: bdCouponPV_nonneg
-- statement:
--   Nonnegative coupons discounted at nonnegative rates have nonnegative market value.
--
--   Mathematical relation:
--
--   $$
--   bdCouponPV\_nonneg
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 2.12–2.13 and 20.13, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.jstor.org/stable/2951677. The proposed model is rooted in Promislow chapter 2.12–2.13 and 20.13. The target Lean identity is an original derivation, not a verbatim published result. Published source page 367 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_bdCouponPV

namespace ActuarialValuation

theorem bdCouponPV_nonneg (D c : ℕ → ℝ) (n : ℕ) (hD : ∀ k∈Finset.range n, 0≤D (k+1)) (hc : ∀ k∈Finset.range n, 0≤c k) : 0≤bdCouponPV D c n := by sorry

end ActuarialValuation
