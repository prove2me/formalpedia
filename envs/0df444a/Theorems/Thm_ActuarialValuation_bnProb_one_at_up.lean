-- Prove2me | Theorems.Thm_ActuarialValuation_bnProb_one_at_up
-- name    : ActuarialValuation.bnProb_one_at_up
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T11:31:22.223162+00:00
-- url     : https://prove2.me/theorems/f3f30544-7ccb-4705-84a5-a31fbaf04dad
-- title:
--   One-period market no-arbitrage and risk-neutral probability: bnProb_one_at_up
-- statement:
--   At the upper gross return boundary, the up-state probability equals one; strict no-arbitrage excludes this boundary.
--
--   Mathematical relation:
--
--   $$
--   bnProb\_one\_at\_up
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 20.1–20.11, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1016/0304-405X(79)90015-1. The proposed model is rooted in Promislow chapter 20.1–20.11. The target Lean identity is an original derivation, not a verbatim published result. Published source page 339 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bnRiskNeutralProb

namespace ActuarialValuation

theorem bnProb_one_at_up (u d : ℝ) (hud : u ≠ d) : bnRiskNeutralProb u d u = 1 := by sorry

end ActuarialValuation
