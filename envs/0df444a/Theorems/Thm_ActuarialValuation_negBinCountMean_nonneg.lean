-- Prove2me | Theorems.Thm_ActuarialValuation_negBinCountMean_nonneg
-- name    : ActuarialValuation.negBinCountMean_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T14:29:53.392242+00:00
-- url     : https://prove2.me/theorems/6ffa31c5-a6bc-4587-9bf0-34de1720fb96
-- title:
--   Valid parameters give nonnegative expected claims
-- statement:
--   Shape r is nonnegative by type, p is nonnegative, and the denominator 1−p is strictly positive under p<1. The resulting expected frequency cannot be negative.
--
--   **Mathematical statement**
--
--   $$
--   0\le p<1\Rightarrow \mu\ge0
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 21, Section 21.5, printed page 383 (Library PDF page 409), parent framework: Section 21.5 (negative-binomial frequency). Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://encyclopediaofmath.org/wiki/Negative_binomial_distribution. The specific Lean declaration ActuarialValuation.negBinCountMean_nonneg is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_negBinCountMean

namespace ActuarialValuation

theorem negBinCountMean_nonneg (r : ℕ) (p : ℝ)
  (hp0 : 0 ≤ p) (hp1 : p < 1) :
  0 ≤ negBinCountMean r p := by sorry

end ActuarialValuation
