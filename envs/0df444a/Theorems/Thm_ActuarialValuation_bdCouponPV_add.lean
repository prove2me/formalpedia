-- Prove2me | Theorems.Thm_ActuarialValuation_bdCouponPV_add
-- name    : ActuarialValuation.bdCouponPV_add
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T11:37:57.578977+00:00
-- url     : https://prove2.me/theorems/30773db0-b0af-4558-a299-9eb7db718a9b
-- title:
--   Coupon-bond cashflows duration and flat yield: bdCouponPV_add
-- statement:
--   Coupon bond valuation is additive across aligned year-end cashflow streams.
--
--   Mathematical relation:
--
--   $$
--   bdCouponPV\_add
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

theorem bdCouponPV_add (D a b : ℕ → ℝ) (n : ℕ) : bdCouponPV D (fun k => a k+b k) n = bdCouponPV D a n + bdCouponPV D b n := by sorry

end ActuarialValuation
