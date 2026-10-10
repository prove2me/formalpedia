-- Prove2me | Theorems.Thm_ActuarialValuation_bnProb_zero_at_down
-- name    : ActuarialValuation.bnProb_zero_at_down
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T11:31:12.053222+00:00
-- url     : https://prove2.me/theorems/b00ebb4b-5a86-46d4-81b5-6dd74c5b1221
-- title:
--   One-period market no-arbitrage and risk-neutral probability: bnProb_zero_at_down
-- statement:
--   At the lower gross return boundary, the up-state martingale probability collapses to zero.
--
--   Mathematical relation:
--
--   $$
--   bnProb\_zero\_at\_down
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 20.1–20.11, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1016/0304-405X(79)90015-1. The proposed model is rooted in Promislow chapter 20.1–20.11. The target Lean identity is an original derivation, not a verbatim published result. Published source page 339 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bnRiskNeutralProb

namespace ActuarialValuation

theorem bnProb_zero_at_down (u d : ℝ) (hud : u ≠ d) : bnRiskNeutralProb u d d = 0 := by sorry

end ActuarialValuation
