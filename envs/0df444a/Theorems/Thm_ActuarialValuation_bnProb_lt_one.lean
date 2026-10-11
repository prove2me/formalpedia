-- Prove2me | Theorems.Thm_ActuarialValuation_bnProb_lt_one
-- name    : ActuarialValuation.bnProb_lt_one
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T11:31:47.393324+00:00
-- url     : https://prove2.me/theorems/73553781-e6a3-474b-8766-f9bc9bce8d09
-- title:
--   One-period market no-arbitrage and risk-neutral probability: bnProb_lt_one
-- statement:
--   The same no-arbitrage ordering forces the martingale probability below one.
--
--   Mathematical relation:
--
--   $$
--   bnProb\_lt\_one
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 20.1–20.11, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1016/0304-405X(79)90015-1. The proposed model is rooted in Promislow chapter 20.1–20.11. The target Lean identity is an original derivation, not a verbatim published result. Published source page 339 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bnRiskNeutralProb

namespace ActuarialValuation

theorem bnProb_lt_one (u d R : ℝ) (h1 : d < R) (h2 : R < u) : bnRiskNeutralProb u d R < 1 := by sorry

end ActuarialValuation
