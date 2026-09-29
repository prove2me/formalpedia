-- Prove2me | solution 1 for talagrand_tangent_sampling_deviation_from_expectation_bound_of_positive_samples_dense
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-06-25T02:37:54.336422+00:00
-- url     : https://prove2.me/submissions/6e249f2d-0ea7-4c2c-8fea-0a6faadb96f3

import Definitions.Def_matrix_completion_talagrand
import Theorems.Thm_talagrand_tangent_sampling_deviation_around_expectation_of_positive_samples_dense
import Theorems.Thm_sum_tangent_sampling_deviation_scales_le_single_scale
import Theorems.Thm_bernoulli_tangent_sampling_deviation_bound_probability_mono
import Theorems.Thm_sample_ratio_between_zero_and_one

open MatrixCompletion

/-
REDUCTION of d55ec3ca_dense
`talagrand_tangent_sampling_deviation_from_expectation_bound_of_positive_samples_dense`
(single-scale output) onto:
  (db094af7_dense) `..._around_expectation_of_positive_samples_dense`
      — gives the deviation-bound probability at the SUM scale
        `scale(Cexpect) + scale(Ctail)`;
  (6b8003d2, PROVED) `sum_tangent_sampling_deviation_scales_le_single_scale`
      — combines the two scales into a single `scale(C)`;
  (27aef870, PROVED) `bernoulli_tangent_sampling_deviation_bound_probability_mono`
      — lifts the event-probability bound from the smaller sum-scale to `scale(C)`;
  (c0188309, PROVED) `sample_ratio_between_zero_and_one`
      — supplies `p ∈ [0,1]` for the monotonicity step.

The reduction body is sorry-free; only db094af7_dense (Open core) carries sorry.

Source: CR2009 Thm 4.1/4.2 (single closed-form scale `C·√(μ₀ n r β log n / m)`).
-/

theorem solution
    (Cexpect : ℝ) :
    0 < Cexpect →
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → 0 < m → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥ β * μ₀ * (↑(max n₁ n₂)) * (r : ℝ) *
          Real.log (↑(max n₁ n₂)) →
        bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              tangentSamplingDeviation Omega S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
          tangentSamplingDeviationScale Cexpect β μ₀ (max n₁ n₂) r m →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              TangentSamplingDeviationBound Omega S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (tangentSamplingDeviationScale C β μ₀ (max n₁ n₂) r m)) ≥
          1 - c * Real.rpow (↑(max n₁ n₂)) (-β) := by
  intro hCexpect
  obtain ⟨Ctail, c, hCtail0, hc0, hAround⟩ :=
    talagrand_tangent_sampling_deviation_around_expectation_of_positive_samples_dense
      Cexpect hCexpect
  obtain ⟨C, hC0, hSum⟩ :=
    sum_tangent_sampling_deviation_scales_le_single_scale Cexpect Ctail hCexpect hCtail0
  refine ⟨C, c, hC0, hc0, ?_⟩
  intro β hβ n₁ n₂ r m M μ₀ μ₁ S hn₁ hn₂ hr hm0 hm hμ₀ hμ₁ hA0 hA1 hdens hEZ
  set p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)) with hp
  have hpr := sample_ratio_between_zero_and_one n₁ n₂ m hn₁ hn₂ hm
  have hp0 : 0 ≤ p := hpr.1
  have hp1 : p ≤ 1 := hpr.2
  -- the around_expectation bound at the SUM scale
  have hbound :=
    hAround β hβ n₁ n₂ r m M μ₀ μ₁ S hn₁ hn₂ hr hm0 hm hμ₀ hμ₁ hA0 hA1 hdens hEZ
  -- lift from the sum scale to the single scale C via monotonicity
  have hle :
      tangentSamplingDeviationScale Cexpect β μ₀ (max n₁ n₂) r m +
          tangentSamplingDeviationScale Ctail β μ₀ (max n₁ n₂) r m ≤
        tangentSamplingDeviationScale C β μ₀ (max n₁ n₂) r m :=
    hSum β μ₀ (max n₁ n₂) r m
  exact
    bernoulli_tangent_sampling_deviation_bound_probability_mono (S := S)
      p
      (tangentSamplingDeviationScale Cexpect β μ₀ (max n₁ n₂) r m +
        tangentSamplingDeviationScale Ctail β μ₀ (max n₁ n₂) r m)
      (tangentSamplingDeviationScale C β μ₀ (max n₁ n₂) r m)
      c β hp0 hp1 hle hbound
