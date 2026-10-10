-- Prove2me | Theorems.Thm_ActuarialValuation_negBinCountVariance_ge_mean
-- name    : ActuarialValuation.negBinCountVariance_ge_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T14:30:26.057991+00:00
-- url     : https://prove2.me/theorems/4ad8e64d-99c5-43b7-9a5d-25069348c123
-- title:
--   Negative-binomial count variance is at least its mean
-- statement:
--   For a valid count parameter, mean and variance differ by r p²/(1−p)²≥0. This provides the precise algebraic overdispersion comparison with a Poisson frequency distribution of the same mean.
--
--   **Mathematical statement**
--
--   $$
--   \sigma^2-\mu=rp^2/(1-p)^2\ge0
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 21, Section 21.5, printed page 383 (Library PDF page 409), parent framework: Section 21.5 (negative-binomial frequency). Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://encyclopediaofmath.org/wiki/Negative_binomial_distribution. The specific Lean declaration ActuarialValuation.negBinCountVariance_ge_mean is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_negBinCountMean
import Definitions.Def_actuarial_negBinCountVariance

namespace ActuarialValuation

theorem negBinCountVariance_ge_mean (r : ℕ) (p : ℝ)
  (hp0 : 0 ≤ p) (hp1 : p < 1) :
  negBinCountMean r p ≤ negBinCountVariance r p := by sorry

end ActuarialValuation
