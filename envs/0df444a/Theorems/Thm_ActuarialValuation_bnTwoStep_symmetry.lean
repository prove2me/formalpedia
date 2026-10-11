-- Prove2me | Theorems.Thm_ActuarialValuation_bnTwoStep_symmetry
-- name    : ActuarialValuation.bnTwoStep_symmetry
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T11:37:33.062376+00:00
-- url     : https://prove2.me/theorems/f9c52093-59a1-456c-b0c1-35084a335b45
-- title:
--   Two-period binomial recursion and American option exercise: bnTwoStep_symmetry
-- statement:
--   Swapping ordered middle paths does not alter their equal two-step risk-neutral weights.
--
--   Mathematical relation:
--
--   $$
--   bnTwoStep\_symmetry
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 20.1–20.11, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1016/0304-405X(79)90015-1. The proposed model is rooted in Promislow chapter 20.1–20.11. The target Lean identity is an original derivation, not a verbatim published result. Published source page 339 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bnTwoStepPrice

namespace ActuarialValuation

theorem bnTwoStep_symmetry (R q uu ud du dd : ℝ) : bnTwoStepPrice R q uu ud du dd = bnTwoStepPrice R q uu du ud dd := by sorry

end ActuarialValuation
