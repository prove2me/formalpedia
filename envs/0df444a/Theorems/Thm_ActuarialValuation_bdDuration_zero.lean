-- Prove2me | Theorems.Thm_ActuarialValuation_bdDuration_zero
-- name    : ActuarialValuation.bdDuration_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:39:23.137122+00:00
-- url     : https://prove2.me/theorems/d6030ebb-412e-4ada-ab46-37b4a5d1f429
-- title:
--   Coupon-bond cashflows duration and flat yield: bdDuration_zero
-- statement:
--   A bond with no payment dates has zero duration numerator, though duration itself requires a nonzero total PV.
--
--   Mathematical relation:
--
--   $$
--   bdDuration\_zero
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 2.12–2.13 and 20.13, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.jstor.org/stable/2951677. The proposed model is rooted in Promislow chapter 2.12–2.13 and 20.13. The target Lean identity is an original derivation, not a verbatim published result. Published source page 367 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_bdDurationNumerator

namespace ActuarialValuation

theorem bdDuration_zero (D c : ℕ → ℝ) : bdDurationNumerator D c 0 = 0 := by sorry

end ActuarialValuation
