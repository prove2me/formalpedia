-- Prove2me | Theorems.Thm_ActuarialValuation_bdForwardState_unique
-- name    : ActuarialValuation.bdForwardState_unique
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:42:32.059854+00:00
-- url     : https://prove2.me/theorems/a73305b5-ef25-4859-8314-9da2934f82c7
-- title:
--   Finite-state stochastic discount factors and arbitrage-free valuation: bdForwardState_unique
-- statement:
--   With a nonzero price of the certain delivery bond, a zero-value forward contract has a unique fair forward delivery price.
--
--   Mathematical relation:
--
--   $$
--   bdForwardState\_unique
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

theorem bdForwardState_unique {m : ℕ} (p discount delivery : Fin m → ℝ) (K : ℝ) (h : bdStateZeroBond p discount ≠ 0) (hzero : bdForwardStatePayment p discount delivery K = 0) : K = bdRiskNeutralForward p discount delivery := by sorry

end ActuarialValuation
