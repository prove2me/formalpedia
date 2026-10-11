-- Prove2me | Theorems.Thm_ActuarialValuation_bnTwoStep_const
-- name    : ActuarialValuation.bnTwoStep_const
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T11:37:57.936716+00:00
-- url     : https://prove2.me/theorems/2c0fae8e-24d3-4c40-a9f2-3290123d047f
-- title:
--   Two-period binomial recursion and American option exercise: bnTwoStep_const
-- statement:
--   A certain two-period payout is discounted by two one-period bank accumulation factors.
--
--   Mathematical relation:
--
--   $$
--   bnTwoStep\_const
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 20.1–20.11, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1016/0304-405X(79)90015-1. The proposed model is rooted in Promislow chapter 20.1–20.11. The target Lean identity is an original derivation, not a verbatim published result. Published source page 339 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bnTwoStepPrice

namespace ActuarialValuation

theorem bnTwoStep_const (R q x : ℝ) (hR : R ≠ 0) : bnTwoStepPrice R q x x x x = x/(R*R) := by sorry

end ActuarialValuation
