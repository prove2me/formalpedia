-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a25_factorial_moments_positive_mgf_identity_positive_rate_20261115
-- name    : AvramDividend.Classical.avram_a25_factorial_moments_positive_mgf_identity_positive_rate_20261115
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T07:25:39.89351+00:00
-- url     : https://prove2.me/theorems/655984e1-0ec2-4df7-a75e-d5f3d3989320
-- title:
--   All factorial moments of a natural count yield its positive-ray exponential MGF and integrability (strictly positive rate)
-- statement:
--   A natural-valued measurable random variable whose descending factorial moments are all r^n has finite positive exponential moments and E exp(theta K)=exp(r(exp theta−1)) for every theta>0. Expand (1+z)^K using the finite binomial theorem, z=exp(theta)−1≥0. Tonelli exchanges the nonnegative sum and integral, and ∫choose(K,n)=r^n/n!. The exponential power series gives the stated finite value; deduce integrability from the nonnegative finite integral. This is an abstract probability result, independent of any Lévy process. Require r>0 to exclude the invalid zero-rate case where all non-integrable nonnegative factorial-moment Bochner integrals default to zero.
-- source:
--   Binomial theorem, Tonelli for nonnegative count functions, exponential power series and descending factorial moments.

import Mathlib
open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal Nat
noncomputable section

theorem AvramDividend.Classical.avram_a25_factorial_moments_positive_mgf_identity_positive_rate_20261115
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K)
    (r : ℝ≥0) (hr : 0 < r)
    (hMom : ∀ n : ℕ,
      (∫ ω, (Nat.descFactorial (K ω) n : ℝ) ∂P) = (r : ℝ) ^ n) :
    ∀ θ : ℝ, 0 < θ →
      Integrable (fun ω => Real.exp (θ * (K ω : ℝ))) P ∧
      (∫ ω, Real.exp (θ * (K ω : ℝ)) ∂P) =
        Real.exp ((r : ℝ) * (Real.exp θ - 1)) := by sorry
