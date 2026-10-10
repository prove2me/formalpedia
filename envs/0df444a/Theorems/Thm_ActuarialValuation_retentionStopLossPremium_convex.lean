-- Prove2me | Theorems.Thm_ActuarialValuation_retentionStopLossPremium_convex
-- name    : ActuarialValuation.retentionStopLossPremium_convex
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T18:15:03.197262+00:00
-- url     : https://prove2.me/theorems/7d609bb2-2ab2-40b8-b3b6-1019a9a1c419
-- title:
--   Finite weighted stop-loss premium is convex in attachment
-- statement:
--   This is an original derived actuarial theorem, based on the stop-loss premium as expectation of positive excess. Nonnegative averaging of pointwise convex reinsurance indemnities preserves convexity of the stop-loss premium curve. All financial amounts, exposure conditions and finite boundaries are given precisely by the Lean declaration; the result is not an assertion that this specific Lean statement has already been proved in the source.
--
--   Mathematical statement:
--
--   $$
--   \Pi(d_\theta)\le(1-\theta)\Pi(a)+\theta\Pi(b)
--   $$
-- source:
--   Original derived actuarial formalisation; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd ed., printed page 409 (https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/). Parent framework: actuarial stop-loss transform and decreasing convex premium as retention varies, supporting source https://www.researchgate.net/publication/4958878_The_Concept_of_Comonotonicity_in_Actuarial_Science_And_Finance_Theory. The Lean declaration ActuarialValuation.retentionStopLossPremium_convex is an original derived finite or algebraic specialisation, not a verbatim numbered published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_retentionStopLossPremium
import Definitions.Def_actuarial_retentionBlend

namespace ActuarialValuation

theorem retentionStopLossPremium_convex
  (w X : ℕ → ℝ) (B : ℕ) (a b θ : ℝ)
  (hw : ∀ s, 0 ≤ w s)
  (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) :
  retentionStopLossPremium w X B (retentionBlend a b θ) ≤
    (1 - θ) * retentionStopLossPremium w X B a +
      θ * retentionStopLossPremium w X B b := by sorry

end ActuarialValuation
