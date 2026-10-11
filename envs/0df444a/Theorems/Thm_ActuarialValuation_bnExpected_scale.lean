-- Prove2me | Theorems.Thm_ActuarialValuation_bnExpected_scale
-- name    : ActuarialValuation.bnExpected_scale
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T11:33:06.246979+00:00
-- url     : https://prove2.me/theorems/582746a1-acf9-4d41-a4a6-2e8592fa2d9e
-- title:
--   One-period market no-arbitrage and risk-neutral probability: bnExpected_scale
-- statement:
--   Risk-neutral expected payoff is homogeneous in a monetary scaling factor.
--
--   Mathematical relation:
--
--   $$
--   bnExpected\_scale
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 20.1–20.11, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1016/0304-405X(79)90015-1. The proposed model is rooted in Promislow chapter 20.1–20.11. The target Lean identity is an original derivation, not a verbatim published result. Published source page 339 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bnExpectedPayoff

namespace ActuarialValuation

theorem bnExpected_scale (q x y a : ℝ) : bnExpectedPayoff q (a*x) (a*y) = a*bnExpectedPayoff q x y := by sorry

end ActuarialValuation
