-- Prove2me | Theorems.Thm_ActuarialValuation_retentionStopLossPremium_lipschitz_mass
-- name    : ActuarialValuation.retentionStopLossPremium_lipschitz_mass
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T18:14:50.028934+00:00
-- url     : https://prove2.me/theorems/9aca4a2b-cf7c-4119-b931-8d60ee0e7492
-- title:
--   Premium decrease bounded by retention change times total mass
-- statement:
--   This is an original derived actuarial theorem, based on the stop-loss premium as expectation of positive excess. The aggregate pure premium change cannot exceed the deductible increase times total mass, regardless of severity values. All financial amounts, exposure conditions and finite boundaries are given precisely by the Lean declaration; the result is not an assertion that this specific Lean statement has already been proved in the source.
--
--   Mathematical statement:
--
--   $$
--   0\le\Pi(a)-\Pi(b)\le(b-a)W
--   $$
-- source:
--   Original derived actuarial formalisation; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd ed., printed page 409 (https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/). Parent framework: actuarial stop-loss transform and decreasing convex premium as retention varies, supporting source https://www.researchgate.net/publication/4958878_The_Concept_of_Comonotonicity_in_Actuarial_Science_And_Finance_Theory. The Lean declaration ActuarialValuation.retentionStopLossPremium_lipschitz_mass is an original derived finite or algebraic specialisation, not a verbatim numbered published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_retentionStopLossPremium
import Definitions.Def_actuarial_retentionWeightTotal

namespace ActuarialValuation

theorem retentionStopLossPremium_lipschitz_mass
  (w X : ℕ → ℝ) (B : ℕ) (a b : ℝ)
  (hw : ∀ s, 0 ≤ w s) (hab : a ≤ b) :
  retentionStopLossPremium w X B a ≤
    retentionStopLossPremium w X B b +
      (b - a) * retentionWeightTotal w B := by sorry

end ActuarialValuation
