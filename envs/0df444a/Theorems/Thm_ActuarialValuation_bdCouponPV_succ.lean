-- Prove2me | Theorems.Thm_ActuarialValuation_bdCouponPV_succ
-- name    : ActuarialValuation.bdCouponPV_succ
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:37:40.286759+00:00
-- url     : https://prove2.me/theorems/aac559be-026b-4d41-bbc8-c5e8a76864fc
-- title:
--   Coupon-bond cashflows duration and flat yield: bdCouponPV_succ
-- statement:
--   Adding the next coupon date adds its discounted cashflow to bond present value.
--
--   Mathematical relation:
--
--   $$
--   bdCouponPV\_succ
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

theorem bdCouponPV_succ (D c : ℕ → ℝ) (n : ℕ) : bdCouponPV D c (n+1) = bdCouponPV D c n + c n * D (n+1) := by sorry

end ActuarialValuation
