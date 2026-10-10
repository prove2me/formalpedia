-- Prove2me | Theorems.Thm_ActuarialValuation_retentionStopLossPremium_zero_weight
-- name    : ActuarialValuation.retentionStopLossPremium_zero_weight
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T16:47:09.620786+00:00
-- url     : https://prove2.me/theorems/768b0217-e7df-44cc-a436-e15e2a629639
-- title:
--   Zero scenario weights give zero pure premium
-- statement:
--   This is an original derived actuarial theorem, based on the stop-loss premium as expectation of positive excess. With no scenario mass, a finite net premium is zero regardless of loss amounts and attachment. All financial amounts, exposure conditions and finite boundaries are given precisely by the Lean declaration; the result is not an assertion that this specific Lean statement has already been proved in the source.
--
--   Mathematical statement:
--
--   $$
--   w_s\equiv0\Longrightarrow\Pi(d)=0
--   $$
-- source:
--   Original derived actuarial formalisation; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd ed., printed page 409 (https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/). Parent framework: actuarial stop-loss transform and decreasing convex premium as retention varies, supporting source https://www.researchgate.net/publication/4958878_The_Concept_of_Comonotonicity_in_Actuarial_Science_And_Finance_Theory. The Lean declaration ActuarialValuation.retentionStopLossPremium_zero_weight is an original derived finite or algebraic specialisation, not a verbatim numbered published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_retentionStopLossPremium

namespace ActuarialValuation

theorem retentionStopLossPremium_zero_weight
  (X : ℕ → ℝ) (B : ℕ) (d : ℝ) :
  retentionStopLossPremium (fun _ => 0) X B d = 0 := by sorry

end ActuarialValuation
