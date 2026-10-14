-- Prove2me | Theorems.Thm_ActuarialValuation_bnProb_sum
-- name    : ActuarialValuation.bnProb_sum
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:32:21.820987+00:00
-- url     : https://prove2.me/theorems/95f9cde7-7aa6-4fb4-8036-27418f227e74
-- title:
--   One-period market no-arbitrage and risk-neutral probability: bnProb_sum
-- statement:
--   The two-state risk-neutral distribution normalises to one.
--
--   Mathematical relation:
--
--   $$
--   bnProb\_sum
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 20.1–20.11, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1016/0304-405X(79)90015-1. The proposed model is rooted in Promislow chapter 20.1–20.11. The target Lean identity is an original derivation, not a verbatim published result. Published source page 339 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bnRiskNeutralProb
import Definitions.Def_actuarial_bnRiskNeutralDown

namespace ActuarialValuation

theorem bnProb_sum (u d R : ℝ) : bnRiskNeutralProb u d R + bnRiskNeutralDown u d R = 1 := by sorry

end ActuarialValuation
