-- Prove2me | Theorems.Thm_ActuarialValuation_bnProb_positive
-- name    : ActuarialValuation.bnProb_positive
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T11:31:31.83098+00:00
-- url     : https://prove2.me/theorems/622e5bf7-0b49-45d9-a6e5-88581beab912
-- title:
--   One-period market no-arbitrage and risk-neutral probability: bnProb_positive
-- statement:
--   Strict down–bank–up ordering implies a strictly positive risk-neutral up probability.
--
--   Mathematical relation:
--
--   $$
--   bnProb\_positive
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 20.1–20.11, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1016/0304-405X(79)90015-1. The proposed model is rooted in Promislow chapter 20.1–20.11. The target Lean identity is an original derivation, not a verbatim published result. Published source page 339 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bnRiskNeutralProb

namespace ActuarialValuation

theorem bnProb_positive (u d R : ℝ) (h1 : d < R) (h2 : R < u) : 0 < bnRiskNeutralProb u d R := by sorry

end ActuarialValuation
