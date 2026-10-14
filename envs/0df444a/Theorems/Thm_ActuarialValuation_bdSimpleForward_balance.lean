-- Prove2me | Theorems.Thm_ActuarialValuation_bdSimpleForward_balance
-- name    : ActuarialValuation.bdSimpleForward_balance
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:34:47.726538+00:00
-- url     : https://prove2.me/theorems/94983130-20b6-4253-a888-d96909cd030b
-- title:
--   Deterministic zero-coupon bonds and forward discounts: bdSimpleForward_balance
-- statement:
--   Net full-interval forward rate plus one reconstructs the forward gross return.
--
--   Mathematical relation:
--
--   $$
--   bdSimpleForward\_balance
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 2.12–2.13 and 20.13, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.jstor.org/stable/2951677. The proposed model is rooted in Promislow chapter 2.12–2.13 and 20.13. The target Lean identity is an original derivation, not a verbatim published result. Published source page 367 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_bdSimpleForward
import Definitions.Def_actuarial_bdForwardGross

namespace ActuarialValuation

theorem bdSimpleForward_balance (D : ℕ → ℝ) (s t : ℕ) : bdSimpleForward D s t + 1 = bdForwardGross D s t := by sorry

end ActuarialValuation
