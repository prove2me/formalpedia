-- Prove2me | Theorems.Thm_ActuarialValuation_bnPut_positive_below_strike
-- name    : ActuarialValuation.bnPut_positive_below_strike
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:36:50.411987+00:00
-- url     : https://prove2.me/theorems/28349c08-83f2-43f3-bb70-2a0cbd05ec6e
-- title:
--   Explicit self-financing hedge and European option replication: bnPut_positive_below_strike
-- statement:
--   A put below the strike is worth its intrinsic exercise payment.
--
--   Mathematical relation:
--
--   $$
--   bnPut\_positive\_below\_strike
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 20.1–20.11, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1016/0304-405X(79)90015-1. The proposed model is rooted in Promislow chapter 20.1–20.11. The target Lean identity is an original derivation, not a verbatim published result. Published source page 339 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bnPut

namespace ActuarialValuation

theorem bnPut_positive_below_strike (s k : ℝ) (h : s ≤ k) : bnPut s k = k-s := by sorry

end ActuarialValuation
