-- Prove2me | Theorems.Thm_ActuarialValuation_retentionStopLossPremium_nonneg
-- name    : ActuarialValuation.retentionStopLossPremium_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T16:46:50.535272+00:00
-- url     : https://prove2.me/theorems/eb292d21-f0c3-4877-9822-fab8054406e9
-- title:
--   Expected positive excess has nonnegative pure premium
-- statement:
--   This is an original derived actuarial theorem, based on the stop-loss premium as expectation of positive excess. Nonnegative probability weights and positive-part claims imply the stop-loss expected ceded cost cannot be negative. All financial amounts, exposure conditions and finite boundaries are given precisely by the Lean declaration; the result is not an assertion that this specific Lean statement has already been proved in the source.
--
--   Mathematical statement:
--
--   $$
--   w_s\ge0\Longrightarrow\Pi(d)\ge0
--   $$
-- source:
--   Original derived actuarial formalisation; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd ed., printed page 409 (https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/). Parent framework: actuarial stop-loss transform and decreasing convex premium as retention varies, supporting source https://www.researchgate.net/publication/4958878_The_Concept_of_Comonotonicity_in_Actuarial_Science_And_Finance_Theory. The Lean declaration ActuarialValuation.retentionStopLossPremium_nonneg is an original derived finite or algebraic specialisation, not a verbatim numbered published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_retentionStopLossPremium

namespace ActuarialValuation

theorem retentionStopLossPremium_nonneg
  (w X : ℕ → ℝ) (B : ℕ) (d : ℝ)
  (hw : ∀ s, 0 ≤ w s) :
  0 ≤ retentionStopLossPremium w X B d := by sorry

end ActuarialValuation
