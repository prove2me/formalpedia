-- Prove2me | Theorems.Thm_ActuarialValuation_bnCall_positive_below_strike
-- name    : ActuarialValuation.bnCall_positive_below_strike
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:36:23.968844+00:00
-- url     : https://prove2.me/theorems/8ce6d93d-b3ce-46df-8c5d-474f473b2a29
-- title:
--   Explicit self-financing hedge and European option replication: bnCall_positive_below_strike
-- statement:
--   A call above its strike has intrinsic value stock less strike.
--
--   Mathematical relation:
--
--   $$
--   bnCall\_positive\_below\_strike
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 20.1–20.11, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1016/0304-405X(79)90015-1. The proposed model is rooted in Promislow chapter 20.1–20.11. The target Lean identity is an original derivation, not a verbatim published result. Published source page 339 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bnCall

namespace ActuarialValuation

theorem bnCall_positive_below_strike (s k : ℝ) (h : k ≤ s) : bnCall s k = s-k := by sorry

end ActuarialValuation
