-- Prove2me | Theorems.Thm_ActuarialValuation_retentionExcessPositive_convex
-- name    : ActuarialValuation.retentionExcessPositive_convex
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T16:46:38.345968+00:00
-- url     : https://prove2.me/theorems/bb67dc4c-3e75-46da-ada1-6ab785e116ce
-- title:
--   Positive excess is convex as a function of retention
-- statement:
--   This is an original derived actuarial theorem, based on the stop-loss premium as expectation of positive excess. Convexity of maximum of affine functions gives Jensen's inequality pointwise for any two retentions and a unit-interval interpolation. All financial amounts, exposure conditions and finite boundaries are given precisely by the Lean declaration; the result is not an assertion that this specific Lean statement has already been proved in the source.
--
--   Mathematical statement:
--
--   $$
--   (x-d_\theta)_+\le(1-\theta)(x-a)_++\theta(x-b)_+
--   $$
-- source:
--   Original derived actuarial formalisation; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd ed., printed page 409 (https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/). Parent framework: actuarial stop-loss transform and decreasing convex premium as retention varies, supporting source https://www.researchgate.net/publication/4958878_The_Concept_of_Comonotonicity_in_Actuarial_Science_And_Finance_Theory. The Lean declaration ActuarialValuation.retentionExcessPositive_convex is an original derived finite or algebraic specialisation, not a verbatim numbered published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_retentionExcessPositive
import Definitions.Def_actuarial_retentionBlend

namespace ActuarialValuation

theorem retentionExcessPositive_convex
  (x a b θ : ℝ) (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) :
  retentionExcessPositive x (retentionBlend a b θ) ≤
    (1 - θ) * retentionExcessPositive x a +
      θ * retentionExcessPositive x b := by sorry

end ActuarialValuation
