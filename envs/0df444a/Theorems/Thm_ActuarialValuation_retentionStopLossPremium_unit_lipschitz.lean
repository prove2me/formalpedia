-- Prove2me | Theorems.Thm_ActuarialValuation_retentionStopLossPremium_unit_lipschitz
-- name    : ActuarialValuation.retentionStopLossPremium_unit_lipschitz
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T18:15:16.43634+00:00
-- url     : https://prove2.me/theorems/a0680ab1-8241-418e-9b6a-96cd52e2311d
-- title:
--   Normalized scenario mass yields sharp unit-Lipschitz bound
-- statement:
--   This is an original derived actuarial theorem, based on the stop-loss premium as expectation of positive excess. For a proper finite probability distribution, a one-unit deductible increase can lower net stop-loss premium by at most one monetary unit. All financial amounts, exposure conditions and finite boundaries are given precisely by the Lean declaration; the result is not an assertion that this specific Lean statement has already been proved in the source.
--
--   Mathematical statement:
--
--   $$
--   W=1,\ a\le b\Longrightarrow\Pi(a)-\Pi(b)\le b-a
--   $$
-- source:
--   Original derived actuarial formalisation; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd ed., printed page 409 (https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/). Parent framework: actuarial stop-loss transform and decreasing convex premium as retention varies, supporting source https://www.researchgate.net/publication/4958878_The_Concept_of_Comonotonicity_in_Actuarial_Science_And_Finance_Theory. The Lean declaration ActuarialValuation.retentionStopLossPremium_unit_lipschitz is an original derived finite or algebraic specialisation, not a verbatim numbered published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_retentionStopLossPremium
import Definitions.Def_actuarial_retentionWeightTotal

namespace ActuarialValuation

theorem retentionStopLossPremium_unit_lipschitz
  (w X : ℕ → ℝ) (B : ℕ) (a b : ℝ)
  (hw : ∀ s, 0 ≤ w s) (hW : retentionWeightTotal w B = 1)
  (hab : a ≤ b) :
  retentionStopLossPremium w X B a ≤
    retentionStopLossPremium w X B b + (b - a) := by sorry

end ActuarialValuation
