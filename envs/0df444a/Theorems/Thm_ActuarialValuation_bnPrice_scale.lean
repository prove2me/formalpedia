-- Prove2me | Theorems.Thm_ActuarialValuation_bnPrice_scale
-- name    : ActuarialValuation.bnPrice_scale
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T11:34:32.991895+00:00
-- url     : https://prove2.me/theorems/447b38d6-530e-42ba-b73a-16b06e775ce8
-- title:
--   One-period market no-arbitrage and risk-neutral probability: bnPrice_scale
-- statement:
--   The binomial claim price is linear in the payoff amount.
--
--   Mathematical relation:
--
--   $$
--   bnPrice\_scale
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 20.1–20.11, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1016/0304-405X(79)90015-1. The proposed model is rooted in Promislow chapter 20.1–20.11. The target Lean identity is an original derivation, not a verbatim published result. Published source page 339 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bnOnePeriodPrice

namespace ActuarialValuation

theorem bnPrice_scale (R q xu xd c : ℝ) : bnOnePeriodPrice R q (c*xu) (c*xd) = c*bnOnePeriodPrice R q xu xd := by sorry

end ActuarialValuation
