-- Prove2me | Theorems.Thm_ActuarialValuation_bdForwardDiscount_reconstruct
-- name    : ActuarialValuation.bdForwardDiscount_reconstruct
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:34:13.10897+00:00
-- url     : https://prove2.me/theorems/a68003da-266d-4ba6-bc25-499669a02047
-- title:
--   Deterministic zero-coupon bonds and forward discounts: bdForwardDiscount_reconstruct
-- statement:
--   Spot maturity bond price reconstructs from spot settlement price and the implied forward discount.
--
--   Mathematical relation:
--
--   $$
--   bdForwardDiscount\_reconstruct
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 2.12–2.13 and 20.13, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.jstor.org/stable/2951677. The proposed model is rooted in Promislow chapter 2.12–2.13 and 20.13. The target Lean identity is an original derivation, not a verbatim published result. Published source page 367 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_bdForwardDiscount

namespace ActuarialValuation

theorem bdForwardDiscount_reconstruct (D : ℕ → ℝ) (s t : ℕ) (hs : D s ≠ 0) : bdForwardDiscount D s t * D s = D t := by sorry

end ActuarialValuation
