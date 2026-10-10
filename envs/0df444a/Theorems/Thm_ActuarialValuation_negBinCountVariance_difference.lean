-- Prove2me | Theorems.Thm_ActuarialValuation_negBinCountVariance_difference
-- name    : ActuarialValuation.negBinCountVariance_difference
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T14:30:38.093815+00:00
-- url     : https://prove2.me/theorems/a6524f01-5ff5-4232-b094-41bc9e9c4041
-- title:
--   Overdispersion above the mean has an explicit closed form
-- statement:
--   Subtracting the negative-binomial mean from its variance and simplifying with nonzero denominator 1−p yields a square in the count parameter. For p in the unit interval, the difference is nonnegative.
--
--   **Mathematical statement**
--
--   $$
--   \sigma^2-\mu=rp^2/(1-p)^2
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 21, Section 21.5, printed page 383 (Library PDF page 409), parent framework: Section 21.5 (negative-binomial frequency). Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://encyclopediaofmath.org/wiki/Negative_binomial_distribution. The specific Lean declaration ActuarialValuation.negBinCountVariance_difference is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_negBinCountMean
import Definitions.Def_actuarial_negBinCountVariance

namespace ActuarialValuation

theorem negBinCountVariance_difference (r : ℕ) (p : ℝ)
  (hp : p ≠ 1) :
  negBinCountVariance r p - negBinCountMean r p =
    (r : ℝ) * p ^ 2 / (1 - p) ^ 2 := by sorry

end ActuarialValuation
