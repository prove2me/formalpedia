-- Prove2me | Theorems.Thm_ActuarialValuation_bnDown_positive
-- name    : ActuarialValuation.bnDown_positive
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T11:32:02.105984+00:00
-- url     : https://prove2.me/theorems/ee8af358-0c43-49bf-9ffd-8f0f551fec9b
-- title:
--   One-period market no-arbitrage and risk-neutral probability: bnDown_positive
-- statement:
--   Down-state probability is strictly positive if the stock return straddles bank return.
--
--   Mathematical relation:
--
--   $$
--   bnDown\_positive
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 20.1–20.11, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1016/0304-405X(79)90015-1. The proposed model is rooted in Promislow chapter 20.1–20.11. The target Lean identity is an original derivation, not a verbatim published result. Published source page 339 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bnRiskNeutralDown

namespace ActuarialValuation

theorem bnDown_positive (u d R : ℝ) (h1 : d < R) (h2 : R < u) : 0 < bnRiskNeutralDown u d R := by sorry

end ActuarialValuation
