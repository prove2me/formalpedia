-- Prove2me | Theorems.Thm_ActuarialValuation_bdCouponPV_empty
-- name    : ActuarialValuation.bdCouponPV_empty
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T11:37:26.505929+00:00
-- url     : https://prove2.me/theorems/cb764526-0ebd-4ee5-9b6d-4a49d6f94973
-- title:
--   Coupon-bond cashflows duration and flat yield: bdCouponPV_empty
-- statement:
--   No coupon dates implies no present value.
--
--   Mathematical relation:
--
--   $$
--   bdCouponPV\_empty
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

theorem bdCouponPV_empty (D c : ℕ → ℝ) : bdCouponPV D c 0 = 0 := by sorry

end ActuarialValuation
