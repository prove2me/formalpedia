-- Prove2me | Theorems.Thm_ActuarialValuation_bdForwardBond_fundamental
-- name    : ActuarialValuation.bdForwardBond_fundamental
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:42:52.405995+00:00
-- url     : https://prove2.me/theorems/a1a07db8-a0de-42fe-8af1-81f4f2e4127b
-- title:
--   Deterministic zero-coupon bonds and forward discounts: bdForwardBond_fundamental
-- statement:
--   The deterministic zero-coupon bond capstone proves internally time-consistent spot-to-forward bond prices, the forward-delivery replication funding identity and the exact inverse discount/gross-return relationship without incorrectly treating future stochastic bond prices as deterministic.
--
--   Mathematical relation:
--
--   $$
--   bdForwardBond\_fundamental
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 2.12–2.13 and 20.13, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.jstor.org/stable/2951677. The proposed model is rooted in Promislow chapter 2.12–2.13 and 20.13. The target Lean identity is an original derivation, not a verbatim published result. Published source page 367 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_bdForwardDiscount
import Definitions.Def_actuarial_bdForwardBond
import Definitions.Def_actuarial_bdZeroPrice
import Definitions.Def_actuarial_bdForwardGross

namespace ActuarialValuation

theorem bdForwardBond_fundamental (D : ℕ → ℝ) (s u t : ℕ) (face : ℝ) (hs : D s ≠ 0) (hu : D u ≠ 0) (ht : D t ≠ 0) : (bdForwardDiscount D s u * bdForwardDiscount D u t = bdForwardDiscount D s t) ∧ (bdForwardBond D face s t * D s = bdZeroPrice D face t) ∧ (bdForwardGross D s t * bdForwardDiscount D s t = 1) := by sorry

end ActuarialValuation
