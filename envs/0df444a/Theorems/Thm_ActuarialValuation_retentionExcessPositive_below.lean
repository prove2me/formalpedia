-- Prove2me | Theorems.Thm_ActuarialValuation_retentionExcessPositive_below
-- name    : ActuarialValuation.retentionExcessPositive_below
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T16:45:41.017012+00:00
-- url     : https://prove2.me/theorems/73adb3a0-caf5-4c2d-a663-3b6417f894a4
-- title:
--   No stop-loss cover below real attachment
-- statement:
--   This is an original derived actuarial theorem, based on the stop-loss premium as expectation of positive excess. A claim at or below the attachment produces zero stop-loss indemnity, including the exact equality case. All financial amounts, exposure conditions and finite boundaries are given precisely by the Lean declaration; the result is not an assertion that this specific Lean statement has already been proved in the source.
--
--   Mathematical statement:
--
--   $$
--   x\le d\Longrightarrow(x-d)_+=0
--   $$
-- source:
--   Original derived actuarial formalisation; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd ed., printed page 409 (https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/). Parent framework: actuarial stop-loss transform and decreasing convex premium as retention varies, supporting source https://www.researchgate.net/publication/4958878_The_Concept_of_Comonotonicity_in_Actuarial_Science_And_Finance_Theory. The Lean declaration ActuarialValuation.retentionExcessPositive_below is an original derived finite or algebraic specialisation, not a verbatim numbered published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_retentionExcessPositive

namespace ActuarialValuation

theorem retentionExcessPositive_below (x d : ℝ) (h : x ≤ d) :
  retentionExcessPositive x d = 0 := by sorry

end ActuarialValuation
