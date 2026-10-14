-- Prove2me | Theorems.Thm_ActuarialValuation_bdConvexity_nonneg
-- name    : ActuarialValuation.bdConvexity_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:40:10.173991+00:00
-- url     : https://prove2.me/theorems/b918166f-179d-47f6-bcb6-3173441a7da8
-- title:
--   Coupon-bond cashflows duration and flat yield: bdConvexity_nonneg
-- statement:
--   Second dated cashflow moment is nonnegative under nonnegative cashflow and discount factors.
--
--   Mathematical relation:
--
--   $$
--   bdConvexity\_nonneg
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 2.12–2.13 and 20.13, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.jstor.org/stable/2951677. The proposed model is rooted in Promislow chapter 2.12–2.13 and 20.13. The target Lean identity is an original derivation, not a verbatim published result. Published source page 367 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_bdConvexityNumerator

namespace ActuarialValuation

theorem bdConvexity_nonneg (D c : ℕ → ℝ) (n : ℕ) (hD : ∀ k∈Finset.range n, 0≤D (k+1)) (hc : ∀ k∈Finset.range n, 0≤c k) : 0≤bdConvexityNumerator D c n := by sorry

end ActuarialValuation
