-- Prove2me | Theorems.Thm_ActuarialValuation_bdForwardState_zero
-- name    : ActuarialValuation.bdForwardState_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:42:12.127815+00:00
-- url     : https://prove2.me/theorems/3608ffc6-523b-4f21-b87f-5209bae848da
-- title:
--   Finite-state stochastic discount factors and arbitrage-free valuation: bdForwardState_zero
-- statement:
--   The delivery price equal to the ratio of state-contingent bond values makes the forward payoff have zero issue-time value.
--
--   Mathematical relation:
--
--   $$
--   bdForwardState\_zero
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 2.12–2.13 and 20.13, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.jstor.org/stable/2951677. The proposed model is rooted in Promislow chapter 2.12–2.13 and 20.13. The target Lean identity is an original derivation, not a verbatim published result. Published source page 367 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_bdForwardStatePayment
import Definitions.Def_actuarial_bdRiskNeutralForward
import Definitions.Def_actuarial_bdStateZeroBond

namespace ActuarialValuation

theorem bdForwardState_zero {m : ℕ} (p discount delivery : Fin m → ℝ) (K : ℝ) (h : bdStateZeroBond p discount ≠ 0) : bdForwardStatePayment p discount delivery (bdRiskNeutralForward p discount delivery) = 0 := by sorry

end ActuarialValuation
