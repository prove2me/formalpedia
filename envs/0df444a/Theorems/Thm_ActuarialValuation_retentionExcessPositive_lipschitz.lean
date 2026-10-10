-- Prove2me | Theorems.Thm_ActuarialValuation_retentionExcessPositive_lipschitz
-- name    : ActuarialValuation.retentionExcessPositive_lipschitz
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T16:46:21.169539+00:00
-- url     : https://prove2.me/theorems/460ba2a5-0bac-44d4-99e0-cfe348163f2d
-- title:
--   Pointwise excess payment is one-Lipschitz in deductible
-- statement:
--   This is an original derived actuarial theorem, based on the stop-loss premium as expectation of positive excess. The reimbursement lost by increasing attachment from a to b cannot exceed the increase in attachment itself. All financial amounts, exposure conditions and finite boundaries are given precisely by the Lean declaration; the result is not an assertion that this specific Lean statement has already been proved in the source.
--
--   Mathematical statement:
--
--   $$
--   a\le b\Longrightarrow(x-a)_+-(x-b)_+\le b-a
--   $$
-- source:
--   Original derived actuarial formalisation; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd ed., printed page 409 (https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/). Parent framework: actuarial stop-loss transform and decreasing convex premium as retention varies, supporting source https://www.researchgate.net/publication/4958878_The_Concept_of_Comonotonicity_in_Actuarial_Science_And_Finance_Theory. The Lean declaration ActuarialValuation.retentionExcessPositive_lipschitz is an original derived finite or algebraic specialisation, not a verbatim numbered published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_retentionExcessPositive

namespace ActuarialValuation

theorem retentionExcessPositive_lipschitz
  (x a b : ℝ) (h : a ≤ b) :
  retentionExcessPositive x a ≤
    retentionExcessPositive x b + (b - a) := by sorry

end ActuarialValuation
