-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a25_factorial_series_norm_summable_mean_20261115
-- name    : AvramDividend.Classical.avram_a25_factorial_series_norm_summable_mean_20261115
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T07:36:17.127921+00:00
-- url     : https://prove2.me/theorems/03c54848-6f34-4af8-8a56-17b87213a250
-- title:
--   Scaled factorial-moment coefficient norms sum absolutely and coefficient means sum to exp(rate times z)
-- statement:
--   Given all positive-rate factorial moments and z≥0, the integrals of the positive scaled coefficients (K)_n z^n/n! have summable absolute norms and their summed expectations are exp(rz). Uses a proved source-independent coefficient integrability/expectation helper, positivity, and the exponential series. This is the norm-summability condition needed for Mathlib integral_tsum_of_summable_integral_norm, separated from the pointwise binomial identity.
-- source:
--   NormedSpace.expSeries_div_hasSum_exp, proved scaled factorial coefficient integrals, positivity.

import Mathlib
open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal Nat BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a25_factorial_series_norm_summable_mean_20261115
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (K : Ω → ℕ) (r : ℝ≥0) (hr : 0 < r)
    (hMom : ∀ n : ℕ,
      (∫ ω, (Nat.descFactorial (K ω) n : ℝ) ∂P) = (r : ℝ) ^ n)
    (z : ℝ) (hz : 0 ≤ z) :
    let F : ℕ → Ω → ℝ := fun n ω =>
      (Nat.descFactorial (K ω) n : ℝ) * (z ^ n / (n.factorial : ℝ))
    Summable (fun n : ℕ => ∫ ω, ‖F n ω‖ ∂P) ∧
      (∑' n : ℕ, ∫ ω, F n ω ∂P) = Real.exp ((r : ℝ) * z) := by sorry
