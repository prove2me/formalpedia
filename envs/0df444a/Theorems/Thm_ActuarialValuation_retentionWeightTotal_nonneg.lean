-- Prove2me | Theorems.Thm_ActuarialValuation_retentionWeightTotal_nonneg
-- name    : ActuarialValuation.retentionWeightTotal_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T18:13:52.780854+00:00
-- url     : https://prove2.me/theorems/17e8cb38-a88d-4ef4-9090-508219127f68
-- title:
--   Finite scenario total mass cannot be negative
-- statement:
--   This is an original derived actuarial theorem, based on the stop-loss premium as expectation of positive excess. Nonnegative scenario probability coefficients have nonnegative total mass, including when all coefficients are zero. All financial amounts, exposure conditions and finite boundaries are given precisely by the Lean declaration; the result is not an assertion that this specific Lean statement has already been proved in the source.
--
--   Mathematical statement:
--
--   $$
--   w_s\ge0\Longrightarrow W\ge0
--   $$
-- source:
--   Original derived actuarial formalisation; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd ed., printed page 409 (https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/). Parent framework: actuarial stop-loss transform and decreasing convex premium as retention varies, supporting source https://www.researchgate.net/publication/4958878_The_Concept_of_Comonotonicity_in_Actuarial_Science_And_Finance_Theory. The Lean declaration ActuarialValuation.retentionWeightTotal_nonneg is an original derived finite or algebraic specialisation, not a verbatim numbered published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_retentionWeightTotal

namespace ActuarialValuation

theorem retentionWeightTotal_nonneg
  (w : ℕ → ℝ) (B : ℕ) (hw : ∀ s, 0 ≤ w s) :
  0 ≤ retentionWeightTotal w B := by sorry

end ActuarialValuation
