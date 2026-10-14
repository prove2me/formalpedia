-- Prove2me | Theorems.Thm_ActuarialValuation_bdCouponPV_scale
-- name    : ActuarialValuation.bdCouponPV_scale
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:38:14.064107+00:00
-- url     : https://prove2.me/theorems/fad952ee-7196-49bd-af10-8a3787a97f59
-- title:
--   Coupon-bond cashflows duration and flat yield: bdCouponPV_scale
-- statement:
--   Cashflow present value is homogeneous in payment amounts.
--
--   Mathematical relation:
--
--   $$
--   bdCouponPV\_scale
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

theorem bdCouponPV_scale (D c : ℕ → ℝ) (n : ℕ) (a : ℝ) : bdCouponPV D (fun k => a*c k) n = a*bdCouponPV D c n := by sorry

end ActuarialValuation
