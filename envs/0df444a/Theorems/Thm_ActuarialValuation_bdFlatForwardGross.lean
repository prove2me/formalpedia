-- Prove2me | Theorems.Thm_ActuarialValuation_bdFlatForwardGross
-- name    : ActuarialValuation.bdFlatForwardGross
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T11:37:06.337362+00:00
-- url     : https://prove2.me/theorems/82681396-80b2-4346-8e1b-9f46f40421e1
-- title:
--   Deterministic zero-coupon bonds and forward discounts: bdFlatForwardGross
-- statement:
--   A flat positive-return curve yields the same gross one-year forward at every integer maturity.
--
--   Mathematical relation:
--
--   $$
--   bdFlatForwardGross
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 2.12–2.13 and 20.13, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.jstor.org/stable/2951677. The proposed model is rooted in Promislow chapter 2.12–2.13 and 20.13. The target Lean identity is an original derivation, not a verbatim published result. Published source page 367 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_bdForwardGross
import Definitions.Def_actuarial_bdFlatDiscount

namespace ActuarialValuation

theorem bdFlatForwardGross (R : ℝ) (t : ℕ) (hR : R ≠ 0) : bdForwardGross (bdFlatDiscount R) t (t+1) = R := by sorry

end ActuarialValuation
