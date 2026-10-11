-- Prove2me | Theorems.Thm_ActuarialValuation_bdForwardBond_balance
-- name    : ActuarialValuation.bdForwardBond_balance
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T11:35:29.430062+00:00
-- url     : https://prove2.me/theorems/cacfb037-de90-4a68-9f95-6a196494add5
-- title:
--   Deterministic zero-coupon bonds and forward discounts: bdForwardBond_balance
-- statement:
--   Forward delivery amount multiplied by today's settlement bond discount equals the present value of the certain maturity-t redemption.
--
--   Mathematical relation:
--
--   $$
--   bdForwardBond\_balance
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 2.12–2.13 and 20.13, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.jstor.org/stable/2951677. The proposed model is rooted in Promislow chapter 2.12–2.13 and 20.13. The target Lean identity is an original derivation, not a verbatim published result. Published source page 367 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_bdForwardBond
import Definitions.Def_actuarial_bdZeroPrice

namespace ActuarialValuation

theorem bdForwardBond_balance (D : ℕ → ℝ) (face : ℝ) (s t : ℕ) (hs : D s ≠ 0) : bdForwardBond D face s t * D s = bdZeroPrice D face t := by sorry

end ActuarialValuation
