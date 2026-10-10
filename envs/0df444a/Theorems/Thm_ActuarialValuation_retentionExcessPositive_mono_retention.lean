-- Prove2me | Theorems.Thm_ActuarialValuation_retentionExcessPositive_mono_retention
-- name    : ActuarialValuation.retentionExcessPositive_mono_retention
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T16:46:08.418237+00:00
-- url     : https://prove2.me/theorems/fc46600a-691e-4247-bf31-e33c930be33f
-- title:
--   A higher retention cannot raise one claim's excess payment
-- statement:
--   This is an original derived actuarial theorem, based on the stop-loss premium as expectation of positive excess. For a given underlying claim, increasing the insurer's retention decreases or preserves the ceded amount. All financial amounts, exposure conditions and finite boundaries are given precisely by the Lean declaration; the result is not an assertion that this specific Lean statement has already been proved in the source.
--
--   Mathematical statement:
--
--   $$
--   a\le b\Longrightarrow(x-b)_+\le(x-a)_+
--   $$
-- source:
--   Original derived actuarial formalisation; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd ed., printed page 409 (https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/). Parent framework: actuarial stop-loss transform and decreasing convex premium as retention varies, supporting source https://www.researchgate.net/publication/4958878_The_Concept_of_Comonotonicity_in_Actuarial_Science_And_Finance_Theory. The Lean declaration ActuarialValuation.retentionExcessPositive_mono_retention is an original derived finite or algebraic specialisation, not a verbatim numbered published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_retentionExcessPositive

namespace ActuarialValuation

theorem retentionExcessPositive_mono_retention
  (x a b : ℝ) (h : a ≤ b) :
  retentionExcessPositive x b ≤ retentionExcessPositive x a := by sorry

end ActuarialValuation
