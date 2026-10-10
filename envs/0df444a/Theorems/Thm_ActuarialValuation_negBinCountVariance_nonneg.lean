-- Prove2me | Theorems.Thm_ActuarialValuation_negBinCountVariance_nonneg
-- name    : ActuarialValuation.negBinCountVariance_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T14:30:11.703278+00:00
-- url     : https://prove2.me/theorems/a9b8f021-79ea-40f4-aa26-1ab511c25fbf
-- title:
--   Valid parameters give nonnegative count variance
-- statement:
--   The squared denominator of the negative-binomial variance is positive under p<1, and the numerator r p is nonnegative. The algebraic count variance is therefore nonnegative.
--
--   **Mathematical statement**
--
--   $$
--   0\le p<1\Rightarrow \sigma^2\ge0
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 21, Section 21.5, printed page 383 (Library PDF page 409), parent framework: Section 21.5 (negative-binomial frequency). Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://encyclopediaofmath.org/wiki/Negative_binomial_distribution. The specific Lean declaration ActuarialValuation.negBinCountVariance_nonneg is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_negBinCountVariance

namespace ActuarialValuation

theorem negBinCountVariance_nonneg (r : ℕ) (p : ℝ)
  (hp0 : 0 ≤ p) (hp1 : p < 1) :
  0 ≤ negBinCountVariance r p := by sorry

end ActuarialValuation
