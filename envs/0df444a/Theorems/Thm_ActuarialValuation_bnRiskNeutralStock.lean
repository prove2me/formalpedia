-- Prove2me | Theorems.Thm_ActuarialValuation_bnRiskNeutralStock
-- name    : ActuarialValuation.bnRiskNeutralStock
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:33:33.209649+00:00
-- url     : https://prove2.me/theorems/d8e4b5a1-bf2a-4db8-8f9e-beb7c9914ca5
-- title:
--   One-period market no-arbitrage and risk-neutral probability: bnRiskNeutralStock
-- statement:
--   Discounted expected stock price under the martingale probability equals initial stock value, with denominator nonzero.
--
--   Mathematical relation:
--
--   $$
--   bnRiskNeutralStock
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 20.1–20.11, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1016/0304-405X(79)90015-1. The proposed model is rooted in Promislow chapter 20.1–20.11. The target Lean identity is an original derivation, not a verbatim published result. Published source page 339 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bnExpectedPayoff
import Definitions.Def_actuarial_bnRiskNeutralProb

namespace ActuarialValuation

theorem bnRiskNeutralStock (s u d R : ℝ) (h : u ≠ d) : bnExpectedPayoff (bnRiskNeutralProb u d R) (s*u) (s*d) = s*R := by sorry

end ActuarialValuation
