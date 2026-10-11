-- Prove2me | Theorems.Thm_ActuarialValuation_bnHedge_cost_riskneutral
-- name    : ActuarialValuation.bnHedge_cost_riskneutral
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T11:35:30.871984+00:00
-- url     : https://prove2.me/theorems/332aed64-9e44-40d5-852f-f5393abb4a3b
-- title:
--   Explicit self-financing hedge and European option replication: bnHedge_cost_riskneutral
-- statement:
--   Cost of the explicit self-financing hedge equals the discounted risk-neutral expected payoff.
--
--   Mathematical relation:
--
--   $$
--   bnHedge\_cost\_riskneutral
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 20.1–20.11, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1016/0304-405X(79)90015-1. The proposed model is rooted in Promislow chapter 20.1–20.11. The target Lean identity is an original derivation, not a verbatim published result. Published source page 339 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bnPortfolioCost
import Definitions.Def_actuarial_bnHedgeShares
import Definitions.Def_actuarial_bnHedgeCash
import Definitions.Def_actuarial_bnOnePeriodPrice
import Definitions.Def_actuarial_bnRiskNeutralProb

namespace ActuarialValuation

theorem bnHedge_cost_riskneutral (s u d R xu xd : ℝ) (hs : s ≠ 0) (hud : u ≠ d) (hR : R ≠ 0) : bnPortfolioCost s (bnHedgeShares s u d xu xd) (bnHedgeCash R u d xu xd) = bnOnePeriodPrice R (bnRiskNeutralProb u d R) xu xd := by sorry

end ActuarialValuation
