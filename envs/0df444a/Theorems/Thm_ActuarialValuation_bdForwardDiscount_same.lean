-- Prove2me | Theorems.Thm_ActuarialValuation_bdForwardDiscount_same
-- name    : ActuarialValuation.bdForwardDiscount_same
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T11:33:26.00922+00:00
-- url     : https://prove2.me/theorems/c11a1240-838c-4003-afb6-a1a7fe20b981
-- title:
--   Deterministic zero-coupon bonds and forward discounts: bdForwardDiscount_same
-- statement:
--   No discount applies to a zero-length forward period when the term price is nonzero.
--
--   Mathematical relation:
--
--   $$
--   bdForwardDiscount\_same
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

theorem bdForwardDiscount_same (D : ℕ → ℝ) (t : ℕ) (h : D t ≠ 0) : bdForwardDiscount D t t = 1 := by sorry

end ActuarialValuation
