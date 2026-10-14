-- Prove2me | Theorems.Thm_ActuarialValuation_bnExpected_const
-- name    : ActuarialValuation.bnExpected_const
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:32:37.443597+00:00
-- url     : https://prove2.me/theorems/8fc8416a-be2e-4de7-a19c-90373463755c
-- title:
--   One-period market no-arbitrage and risk-neutral probability: bnExpected_const
-- statement:
--   A deterministic payoff has the same expectation under any two-state weights summing to one.
--
--   Mathematical relation:
--
--   $$
--   bnExpected\_const
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 20.1–20.11, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1016/0304-405X(79)90015-1. The proposed model is rooted in Promislow chapter 20.1–20.11. The target Lean identity is an original derivation, not a verbatim published result. Published source page 339 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bnExpectedPayoff

namespace ActuarialValuation

theorem bnExpected_const (q x : ℝ) : bnExpectedPayoff q x x = x := by sorry

end ActuarialValuation
