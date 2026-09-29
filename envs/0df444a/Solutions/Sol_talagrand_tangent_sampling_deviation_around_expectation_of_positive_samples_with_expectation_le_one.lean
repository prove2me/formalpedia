-- Prove2me | solution 1 for talagrand_tangent_sampling_deviation_around_expectation_of_positive_samples_with_expectation_le_one
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-07-22T16:43:00.261889+00:00
-- url     : https://prove2.me/submissions/41588f04-4f37-46a7-9e00-55c1d7ef8148
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_a0_implies_tangent_sampling_talagrand_increment_and_variance_bounds_min
import Theorems.Thm_talagrand_tangent_sampling_deviation_around_mean_from_increment_variance_bounds_pos_with_expectation_le_one
import Theorems.Thm_bernoulli_tangent_sampling_deviation_bound_probability_mono
import Theorems.Thm_sample_ratio_between_zero_and_one

open MatrixCompletion

/-!
Source: Candes--Recht 2008, PDF p. 19, Theorem 4.2 and equation (4.10),
with Appendix 9.1, PDF p. 46, Theorem 9.1/equation (9.2).

This is the corrected version of the positive-sample around-expectation bridge:
it keeps the Appendix 9.1 proviso `E Z <= 1`, gets the increment and variance
inputs from the positive-sample A0 feed, applies the corrected around-mean
Talagrand child, and then enlarges the event threshold using the separate
Rudelson-scale expectation bound.
-/

theorem solution
    (Cexpect : ℝ) :
    0 < Cexpect →
    ∃ Ctail c : ℝ, 0 < Ctail ∧ 0 < c ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → 0 < m → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              tangentSamplingDeviation Omega S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤ 1 →
        bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              tangentSamplingDeviation Omega S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
          tangentSamplingDeviationScale Cexpect β μ₀ (max n₁ n₂) r m →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              TangentSamplingDeviationBound Omega S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (tangentSamplingDeviationScale Cexpect β μ₀ (max n₁ n₂) r m +
                  tangentSamplingDeviationScale Ctail β μ₀ (max n₁ n₂) r m)) ≥
          1 - c * Real.rpow (↑(max n₁ n₂)) (-β) := by
  intro _hCexpect
  rcases
      talagrand_tangent_sampling_deviation_around_mean_from_increment_variance_bounds_pos_with_expectation_le_one with
    ⟨Ctail, c, hCtail, hc, hAroundMean⟩
  refine ⟨Ctail, c, hCtail, hc, ?_⟩
  intro β hβ n₁ n₂ r m M μ₀ μ₁ S
    hn₁ hn₂ hr hmPos hm hμ₀ hμ₁ hA0 hA1 hExpectationOne hExpectationScale
  let p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))
  rcases
      a0_implies_tangent_sampling_talagrand_increment_and_variance_bounds_min
        n₁ n₂ r m M μ₀ S hn₁ hn₂ hr hmPos hm hμ₀ hA0 with
    ⟨hIncrement, hVariance⟩
  have hMeanProb :
      bernoulliEventProb p
          (fun Omega =>
            TangentSamplingDeviationBound Omega S p
              (bernoulliExpectation p
                  (fun Omega' => tangentSamplingDeviation Omega' S p) +
                tangentSamplingDeviationScale Ctail β μ₀ (max n₁ n₂) r m)) ≥
        1 - c * Real.rpow (↑(max n₁ n₂)) (-β) := by
    simpa [p] using
      hAroundMean β hβ n₁ n₂ r m M μ₀ μ₁ S
        hn₁ hn₂ hr hmPos hm hμ₀ hμ₁ hA0 hA1 hExpectationOne hIncrement hVariance
  have hThreshold :
      bernoulliExpectation p
          (fun Omega' => tangentSamplingDeviation Omega' S p) +
        tangentSamplingDeviationScale Ctail β μ₀ (max n₁ n₂) r m ≤
      tangentSamplingDeviationScale Cexpect β μ₀ (max n₁ n₂) r m +
        tangentSamplingDeviationScale Ctail β μ₀ (max n₁ n₂) r m := by
    exact add_le_add (by simpa [p] using hExpectationScale) le_rfl
  rcases sample_ratio_between_zero_and_one n₁ n₂ m hn₁ hn₂ hm with
    ⟨hpNonneg, hpLeOne⟩
  exact bernoulli_tangent_sampling_deviation_bound_probability_mono S p
    (bernoulliExpectation p
        (fun Omega' => tangentSamplingDeviation Omega' S p) +
      tangentSamplingDeviationScale Ctail β μ₀ (max n₁ n₂) r m)
    (tangentSamplingDeviationScale Cexpect β μ₀ (max n₁ n₂) r m +
      tangentSamplingDeviationScale Ctail β μ₀ (max n₁ n₂) r m)
    c β hpNonneg hpLeOne hThreshold hMeanProb
