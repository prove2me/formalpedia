-- Prove2me | Theorems.Thm_ActuarialValuation_retentionExcessPositive_nonneg
-- name    : ActuarialValuation.retentionExcessPositive_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T16:45:27.083958+00:00
-- url     : https://prove2.me/theorems/7c6c4f52-e1e6-4931-a617-c7b731de3bd0
-- title:
--   Real positive excess payment is nonnegative
-- statement:
--   This is an original derived actuarial theorem, based on the stop-loss premium as expectation of positive excess. An excess loss payment cannot be negative even for signed real inputs, since the positive part is the maximum against zero. All financial amounts, exposure conditions and finite boundaries are given precisely by the Lean declaration; the result is not an assertion that this specific Lean statement has already been proved in the source.
--
--   Mathematical statement:
--
--   $$
--   (x-d)_+\ge0
--   $$
-- source:
--   Original derived actuarial formalisation; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd ed., printed page 409 (https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/). Parent framework: actuarial stop-loss transform and decreasing convex premium as retention varies, supporting source https://www.researchgate.net/publication/4958878_The_Concept_of_Comonotonicity_in_Actuarial_Science_And_Finance_Theory. The Lean declaration ActuarialValuation.retentionExcessPositive_nonneg is an original derived finite or algebraic specialisation, not a verbatim numbered published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_retentionExcessPositive

namespace ActuarialValuation

theorem retentionExcessPositive_nonneg (x d : ℝ) :
  0 ≤ retentionExcessPositive x d := by sorry

end ActuarialValuation
