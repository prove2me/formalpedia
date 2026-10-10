-- Prove2me | Theorems.Thm_ActuarialValuation_retentionStopLossPremium_mono
-- name    : ActuarialValuation.retentionStopLossPremium_mono
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T16:47:29.394158+00:00
-- url     : https://prove2.me/theorems/a6056f72-20e5-4bca-a6b1-bdcf816e654d
-- title:
--   Stop-loss premium decreases as deductible increases
-- statement:
--   This is an original derived actuarial theorem, based on the stop-loss premium as expectation of positive excess. The ceded pure premium is a decreasing function of the insurer's retained attachment for nonnegative scenario masses. All financial amounts, exposure conditions and finite boundaries are given precisely by the Lean declaration; the result is not an assertion that this specific Lean statement has already been proved in the source.
--
--   Mathematical statement:
--
--   $$
--   a\le b\Longrightarrow\Pi(b)\le\Pi(a)
--   $$
-- source:
--   Original derived actuarial formalisation; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd ed., printed page 409 (https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/). Parent framework: actuarial stop-loss transform and decreasing convex premium as retention varies, supporting source https://www.researchgate.net/publication/4958878_The_Concept_of_Comonotonicity_in_Actuarial_Science_And_Finance_Theory. The Lean declaration ActuarialValuation.retentionStopLossPremium_mono is an original derived finite or algebraic specialisation, not a verbatim numbered published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_retentionStopLossPremium

namespace ActuarialValuation

theorem retentionStopLossPremium_mono
  (w X : ℕ → ℝ) (B : ℕ) (a b : ℝ)
  (hw : ∀ s, 0 ≤ w s) (hab : a ≤ b) :
  retentionStopLossPremium w X B b ≤
    retentionStopLossPremium w X B a := by sorry

end ActuarialValuation
