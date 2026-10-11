-- Prove2me | Theorems.Thm_ActuarialValuation_bnExpected_nonnegative
-- name    : ActuarialValuation.bnExpected_nonnegative
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T11:33:18.225086+00:00
-- url     : https://prove2.me/theorems/48ff4cdd-74f6-4fc8-94e7-de5f33458d22
-- title:
--   One-period market no-arbitrage and risk-neutral probability: bnExpected_nonnegative
-- statement:
--   Valid probability weights preserve nonnegative option payoff values.
--
--   Mathematical relation:
--
--   $$
--   bnExpected\_nonnegative
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 20.1–20.11, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1016/0304-405X(79)90015-1. The proposed model is rooted in Promislow chapter 20.1–20.11. The target Lean identity is an original derivation, not a verbatim published result. Published source page 339 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bnExpectedPayoff

namespace ActuarialValuation

theorem bnExpected_nonnegative (q xu xd : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hu : 0 ≤ xu) (hd : 0 ≤ xd) : 0 ≤ bnExpectedPayoff q xu xd := by sorry

end ActuarialValuation
