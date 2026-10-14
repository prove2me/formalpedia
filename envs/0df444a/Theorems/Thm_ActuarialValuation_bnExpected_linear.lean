-- Prove2me | Theorems.Thm_ActuarialValuation_bnExpected_linear
-- name    : ActuarialValuation.bnExpected_linear
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:32:51.809641+00:00
-- url     : https://prove2.me/theorems/c63411ce-dd80-49b6-a98a-33a2ee875fcc
-- title:
--   One-period market no-arbitrage and risk-neutral probability: bnExpected_linear
-- statement:
--   Risk-neutral expectation adds across simultaneous contingent cashflows.
--
--   Mathematical relation:
--
--   $$
--   bnExpected\_linear
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 20.1–20.11, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1016/0304-405X(79)90015-1. The proposed model is rooted in Promislow chapter 20.1–20.11. The target Lean identity is an original derivation, not a verbatim published result. Published source page 339 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bnExpectedPayoff

namespace ActuarialValuation

theorem bnExpected_linear (q x1 y1 x2 y2 : ℝ) : bnExpectedPayoff q (x1+x2) (y1+y2) = bnExpectedPayoff q x1 y1 + bnExpectedPayoff q x2 y2 := by sorry

end ActuarialValuation
