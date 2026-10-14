-- Prove2me | Theorems.Thm_ActuarialValuation_bdDuration_identity
-- name    : ActuarialValuation.bdDuration_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:39:54.492508+00:00
-- url     : https://prove2.me/theorems/82c34751-743e-46e4-83b8-8a38cc042774
-- title:
--   Coupon-bond cashflows duration and flat yield: bdDuration_identity
-- statement:
--   Macaulay duration times total bond present value recovers the time-weighted PV sum if the bond price is nonzero.
--
--   Mathematical relation:
--
--   $$
--   bdDuration\_identity
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 2.12–2.13 and 20.13, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.jstor.org/stable/2951677. The proposed model is rooted in Promislow chapter 2.12–2.13 and 20.13. The target Lean identity is an original derivation, not a verbatim published result. Published source page 367 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_bdMacaulayDuration
import Definitions.Def_actuarial_bdCouponPV
import Definitions.Def_actuarial_bdDurationNumerator

namespace ActuarialValuation

theorem bdDuration_identity (D c : ℕ → ℝ) (n : ℕ) (h : bdCouponPV D c n ≠ 0) : bdMacaulayDuration D c n * bdCouponPV D c n = bdDurationNumerator D c n := by sorry

end ActuarialValuation
