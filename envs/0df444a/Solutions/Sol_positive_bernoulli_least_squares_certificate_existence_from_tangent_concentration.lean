-- Prove2me | solution 1 for positive_bernoulli_least_squares_certificate_existence_from_tangent_concentration
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T09:19:12.809694+00:00
-- url     : https://prove2.me/submissions/49248d69-4e09-412b-a203-6eeeff7c577e

import Theorems.Thm_bernoulli_event_probability_mono
import Theorems.Thm_positive_tangent_sampling_concentration_implies_least_squares_certificate_exists

open MatrixCompletion

theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ} (S : SVD M r)
    (p c β : ℝ) :
    0 < p → p ≤ 1 →
    bernoulliEventProb p
        (fun Omega => TangentSamplingConcentration Omega S p ((1 : ℝ) / 2)) ≥
        1 - c * Real.rpow (↑(max n₁ n₂)) (-β) →
    bernoulliEventProb p
        (fun Omega => ∃ Y : Matrix (Fin n₁) (Fin n₂) ℝ,
          LeastSquaresDualCertificate Omega S Y) ≥
        1 - c * Real.rpow (↑(max n₁ n₂)) (-β) := by
  intro hp hp_one hconc
  have hmono :
      bernoulliEventProb p
          (fun Omega => TangentSamplingConcentration Omega S p ((1 : ℝ) / 2)) ≤
        bernoulliEventProb p
          (fun Omega => ∃ Y : Matrix (Fin n₁) (Fin n₂) ℝ,
            LeastSquaresDualCertificate Omega S Y) :=
    bernoulli_event_probability_mono p
      (fun Omega => TangentSamplingConcentration Omega S p ((1 : ℝ) / 2))
      (fun Omega => ∃ Y : Matrix (Fin n₁) (Fin n₂) ℝ,
        LeastSquaresDualCertificate Omega S Y)
      (le_of_lt hp) hp_one
      (fun Omega hOmega =>
        positive_tangent_sampling_concentration_implies_least_squares_certificate_exists
          Omega S p hp hOmega)
  exact le_trans hconc hmono
