-- Prove2me | Theorems.Thm_ActuarialValuation_bnTwoStep_backwards
-- name    : ActuarialValuation.bnTwoStep_backwards
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T11:37:47.739334+00:00
-- url     : https://prove2.me/theorems/225b7cbf-ad6d-4463-979a-0898b3263fdd
-- title:
--   Two-period binomial recursion and American option exercise: bnTwoStep_backwards
-- statement:
--   Two-step risk-neutral valuation agrees with node-by-node backward induction for nonzero discount return.
--
--   Mathematical relation:
--
--   $$
--   bnTwoStep\_backwards
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 20.1–20.11, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1016/0304-405X(79)90015-1. The proposed model is rooted in Promislow chapter 20.1–20.11. The target Lean identity is an original derivation, not a verbatim published result. Published source page 339 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bnTwoStepBackward
import Definitions.Def_actuarial_bnTwoStepPrice

namespace ActuarialValuation

theorem bnTwoStep_backwards (R q uu ud du dd : ℝ) (hR : R ≠ 0) : bnTwoStepBackward R q uu ud du dd = bnTwoStepPrice R q uu ud du dd := by sorry

end ActuarialValuation
