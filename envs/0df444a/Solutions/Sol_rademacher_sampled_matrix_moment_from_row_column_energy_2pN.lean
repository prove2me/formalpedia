-- Prove2me | solution 1 for rademacher_sampled_matrix_moment_from_row_column_energy_2pN
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-25T09:40:55.904686+00:00
-- url     : https://prove2.me/submissions/c5b8ab26-d117-467b-a8bb-263e7fe3aeea

import Theorems.Thm_rademacher_sampled_matrix_conditional_khintchine_bound
import Theorems.Thm_bernoulli_rademacher_moment_bound_by_conditional_khintchine_scales_of_sample_ratio
import Theorems.Thm_conditional_khintchine_scale_moment_from_row_column_energy_moment_2pN

open MatrixCompletion

/-- Source: Candes-Recht 2008, Section 6.1, PDF p. 24 through PDF p. 25,
from the symmetrization/noncommutative-Khintchine estimate before Lemma 6.2,
Lemma 6.2/equation (6.6), and the paragraph leading to Theorem 6.3/equation
(6.7).

`_2pN` variant: the admissibility window on the exponent is `q ≤ 2·p·n`
(twice the sample-ratio scale) instead of the strict `q ≤ p·n`.  The relaxed
window is exactly what the one-sample lower bound supplies for `q = ⌈β log N⌉`
through the relaxed Lemma 6.2 (binomial card moment at scale `x = 2·n·p`).

The `q ≤ p·n` (and likewise `q ≤ 2·p·n`) hypothesis is DEAD WEIGHT in the
Khintchine conversion: it is never consumed by any analytic step.  The three
genuine sub-results are:
  * `rademacher_sampled_matrix_conditional_khintchine_bound` (needs only
    `1 ≤ q` and `q ≥ β log N`),
  * `bernoulli_rademacher_moment_bound_by_conditional_khintchine_scales_of_sample_ratio`
    (needs only `m ≤ n₁ n₂`),
  * `conditional_khintchine_scale_moment_from_row_column_energy_moment_2pN`
    (the corrected scale-moment bridge; the older scalar bridge was too weak
    in degenerate sample-ratio cases and has been deprecated).
We compose these three directly, so the `q ≤ 2·p·n` hypothesis is intro'd and
dropped, exactly as in the `pN` parent. -/
theorem solution
    (Cenergy : ℝ) :
    0 < Cenergy →
    ∃ Crad : ℝ, 0 < Crad ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ m q : ℕ) (X : Matrix (Fin n₁) (Fin n₂) ℝ),
        0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ →
        (m : ℝ) ≥ β * (↑(max n₁ n₂)) *
          Real.log (↑(max n₁ n₂)) →
        1 ≤ q →
        (q : ℝ) ≥ β * Real.log (↑(max n₁ n₂)) →
        (q : ℝ) ≤ 2 * (β * Real.log (↑(max n₁ n₂))) →
        (q : ℝ) ≤ 2 * (((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
            (↑(max n₁ n₂))) →
        bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              (max (sampledRowEnergyMax Omega X)
                (sampledColumnEnergyMax Omega X)) ^ q) ≤
          (Cenergy * ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
            (↑(max n₁ n₂)) * entrySupNorm X ^ 2) ^ q →
        bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              rademacherExpectation
                (fun eps =>
                  spectralNorm
                    (rademacherSampledMatrix Omega eps
                      ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q)) ≤
          (Crad * Real.sqrt
            (((q : ℝ) * (↑(max n₁ n₂))) /
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
            entrySupNorm X) ^ q := by
  intro hCenergy
  rcases rademacher_sampled_matrix_conditional_khintchine_bound with
    ⟨Ckh, hCkh, hConditionalKhintchine⟩
  rcases conditional_khintchine_scale_moment_from_row_column_energy_moment_2pN
      Cenergy Ckh hCenergy hCkh with
    ⟨Crad, hCrad, hScale⟩
  refine ⟨Crad, hCrad, ?_⟩
  intro β hβ n₁ n₂ m q X hn₁ hn₂ hm hSample hqOne hqLogLower
    hqLogUpper hqSamplingUpper hEnergy
  -- 1. integrate the pointwise conditional Khintchine bound over the sample
  have hRadScale :=
    bernoulli_rademacher_moment_bound_by_conditional_khintchine_scales_of_sample_ratio
      Ckh n₁ n₂ m q X hn₁ hn₂ hm
      (fun Omega =>
        hConditionalKhintchine β hβ n₁ n₂ m q Omega X hqOne
          hqLogLower)
  -- 2. convert the integrated Khintchine scale moment to the displayed scale
  have hScaleFinal :=
    hScale β hβ n₁ n₂ m q X hn₁ hn₂ hm hSample hqOne
      hqLogLower hqLogUpper hqSamplingUpper hEnergy
  exact le_trans hRadScale hScaleFinal
