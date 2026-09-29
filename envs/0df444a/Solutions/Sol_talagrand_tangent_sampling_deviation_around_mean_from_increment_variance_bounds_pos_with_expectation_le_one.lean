-- Prove2me | solution 1 for talagrand_tangent_sampling_deviation_around_mean_from_increment_variance_bounds_pos_with_expectation_le_one
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-07-19T19:00:58.838652+00:00
-- url     : https://prove2.me/submissions/2f470592-06d8-410a-b5e6-a825bb1ffd9c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_talagrand_tangent_sampling_deviation_around_mean_raw_tail_pos_with_expectation_le_one
import Theorems.Thm_talagrand_tangent_sampling_raw_tail_le_deviation_scale
import Theorems.Thm_bernoulli_tangent_sampling_deviation_bound_probability_mono
import Theorems.Thm_sample_ratio_between_zero_and_one

open MatrixCompletion

/-!
Source: Candes--Recht 2008, PDF p. 19, Theorem 4.2/equation (4.10), plus
Appendix 9.1, PDF pp. 46--47, Theorem 9.1/equation (9.2).

This reduction converts the corrected raw Talagrand tail, with `E Z <= 1`, to
the standard Candes--Recht scale after substituting the Appendix 9.1 variance
and increment scale `2 * mu0 * max n1 n2 * r / m`.
-/

theorem solution :
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
        TangentSamplingTalagrandIncrementBound S
          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
          (2 * μ₀ * (↑(max n₁ n₂)) * (r : ℝ) / (m : ℝ)) →
        TangentSamplingTalagrandVarianceBound S
          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
          (2 * μ₀ * (↑(max n₁ n₂)) * (r : ℝ) / (m : ℝ)) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              TangentSamplingDeviationBound Omega S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (bernoulliExpectation
                    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                    (fun Omega' =>
                      tangentSamplingDeviation Omega' S
                        ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) +
                  tangentSamplingDeviationScale Ctail β μ₀ (max n₁ n₂) r m)) ≥
          1 - c * Real.rpow (↑(max n₁ n₂)) (-β) := by
  rcases talagrand_tangent_sampling_deviation_around_mean_raw_tail_pos_with_expectation_le_one with
    ⟨K, c, hK, hc, hRaw⟩
  rcases talagrand_tangent_sampling_raw_tail_le_deviation_scale K hK with
    ⟨Ctail, hCtail, hScale⟩
  refine ⟨Ctail, c, hCtail, hc, ?_⟩
  intro β hβ n₁ n₂ r m M μ₀ μ₁ S hn₁ hn₂ hr hmPos hm hμ₀ hμ₁ hA0 hA1
    hExpectation hIncrement hVariance
  let p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))
  let B : ℝ := 2 * μ₀ * (↑(max n₁ n₂)) * (r : ℝ) / (m : ℝ)
  have hRawProb :
      bernoulliEventProb p
          (fun Omega =>
            TangentSamplingDeviationBound Omega S p
              (bernoulliExpectation p
                  (fun Omega' => tangentSamplingDeviation Omega' S p) +
                K * Real.sqrt (B * (β * Real.log (↑(max n₁ n₂)))))) ≥
        1 - c * Real.rpow (↑(max n₁ n₂)) (-β) := by
    simpa [p, B] using
      hRaw β hβ n₁ n₂ r m M μ₀ μ₁ S
        (2 * μ₀ * (↑(max n₁ n₂)) * (r : ℝ) / (m : ℝ))
        hn₁ hn₂ hr hmPos hm hμ₀ hμ₁ hA0 hA1 hExpectation hIncrement hVariance
  have hTailScale :
      K * Real.sqrt (B * (β * Real.log (↑(max n₁ n₂)))) ≤
        tangentSamplingDeviationScale Ctail β μ₀ (max n₁ n₂) r m := by
    simpa [B, mul_assoc, mul_left_comm, mul_comm] using
      hScale β hβ n₁ n₂ r m μ₀ hn₁ hn₂ hr hμ₀
  have hThreshold :
      bernoulliExpectation p
          (fun Omega' => tangentSamplingDeviation Omega' S p) +
          K * Real.sqrt (B * (β * Real.log (↑(max n₁ n₂)))) ≤
        bernoulliExpectation p
          (fun Omega' => tangentSamplingDeviation Omega' S p) +
          tangentSamplingDeviationScale Ctail β μ₀ (max n₁ n₂) r m := by
    simpa [add_comm, add_left_comm, add_assoc] using
      add_le_add_right hTailScale
        (bernoulliExpectation p
          (fun Omega' => tangentSamplingDeviation Omega' S p))
  rcases sample_ratio_between_zero_and_one n₁ n₂ m hn₁ hn₂ hm with
    ⟨hpNonneg, hpLeOne⟩
  exact bernoulli_tangent_sampling_deviation_bound_probability_mono S p
    (bernoulliExpectation p
        (fun Omega' => tangentSamplingDeviation Omega' S p) +
      K * Real.sqrt (B * (β * Real.log (↑(max n₁ n₂)))))
    (bernoulliExpectation p
        (fun Omega' => tangentSamplingDeviation Omega' S p) +
      tangentSamplingDeviationScale Ctail β μ₀ (max n₁ n₂) r m)
    c β hpNonneg hpLeOne hThreshold hRawProb
