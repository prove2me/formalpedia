-- Prove2me | solution 1 for talagrand_tangent_sampling_absolute_deviation_log_tail
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-29T15:41:31.220057+00:00
-- url     : https://prove2.me/submissions/1b7e8f74-1214-42e7-b006-86158cc8a920

import Theorems.Thm_talagrand_tangent_sampling_supremum_absolute_deviation_log_tail
import Theorems.Thm_tangent_sampling_deviation_eq_talagrand_supremum_deviation_of_nonnegative_rate
import Theorems.Thm_sample_ratio_between_zero_and_one

open MatrixCompletion

/-!
Source: Candes--Recht, Appendix 9.1, PDF p. 46, immediately after equation
(9.2), where `Z` is rewritten as a supremum over Frobenius-unit test matrices.

This sketch transfers the exact logarithmic Talagrand tail from the explicit
supremum variable to the project's `tangentSamplingDeviation`, using the
already-proved nonnegative-rate representation equality.
-/
theorem solution :
    ∃ K : ℝ, 0 < K ∧
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (S : SVD M r) (B sigmaSq t : ℝ),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        0 < B → 0 ≤ sigmaSq → 0 ≤ t →
        TangentSamplingTalagrandIncrementBound S
          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) B →
        TangentSamplingTalagrandVarianceBound S
          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) sigmaSq →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              |tangentSamplingDeviation Omega S
                    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) -
                  bernoulliExpectation
                    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                    (fun Omega' =>
                      tangentSamplingDeviation Omega' S
                        ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))))| ≤ t) ≥
          1 -
            3 * Real.exp
              (-(t / (K * B)) *
                Real.log
                  (1 + (B * t) /
                    (sigmaSq +
                      B * bernoulliExpectation
                        ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                          (fun Omega' =>
                            tangentSamplingDeviation Omega' S
                              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))))))) := by
  rcases talagrand_tangent_sampling_supremum_absolute_deviation_log_tail with
    ⟨K, hK, hSup⟩
  refine ⟨K, hK, ?_⟩
  intro n₁ n₂ r m M S B sigmaSq t hn₁ hn₂ hr hm hB hsigma ht hIncrement hVariance
  let p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))
  have hp_nonneg : 0 ≤ p :=
    (sample_ratio_between_zero_and_one n₁ n₂ m hn₁ hn₂ hm).1
  have hRepresent :
      (fun Omega : Finset (Fin n₁ × Fin n₂) =>
        tangentSamplingDeviation Omega S p) =
      (fun Omega : Finset (Fin n₁ × Fin n₂) =>
        tangentSamplingTalagrandSupremumDeviation Omega S p) :=
    tangent_sampling_deviation_eq_talagrand_supremum_deviation_of_nonnegative_rate
      S p hp_nonneg
  have hPoint :
      ∀ Omega : Finset (Fin n₁ × Fin n₂),
        tangentSamplingTalagrandSupremumDeviation Omega S p =
          tangentSamplingDeviation Omega S p := by
    intro Omega
    exact congrFun hRepresent.symm Omega
  have hProbSup :
      bernoulliEventProb p
          (fun Omega =>
            |tangentSamplingTalagrandSupremumDeviation Omega S p -
              bernoulliExpectation p
                (fun Omega' =>
                  tangentSamplingTalagrandSupremumDeviation Omega' S p)| ≤ t) ≥
        1 -
          3 * Real.exp
            (-(t / (K * B)) *
              Real.log
                (1 + (B * t) /
                  (sigmaSq +
                    B * bernoulliExpectation p
                      (fun Omega' =>
                        tangentSamplingTalagrandSupremumDeviation Omega' S p)))) := by
    simpa [p] using
      hSup n₁ n₂ r m M S B sigmaSq t hn₁ hn₂ hr hm hB hsigma ht
        hIncrement hVariance
  simpa [hPoint, p] using hProbSup
