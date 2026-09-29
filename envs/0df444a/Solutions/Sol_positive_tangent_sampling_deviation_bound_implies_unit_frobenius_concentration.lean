-- Prove2me | solution 1 for positive_tangent_sampling_deviation_bound_implies_unit_frobenius_concentration
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T06:42:39.608179+00:00
-- url     : https://prove2.me/submissions/912cced3-1612-4a81-af3b-5f61471517e4

import Theorems.Thm_positive_tangent_sampling_deviation_bound_implies_unit_frobenius_concentration_of_bddAbove
import Theorems.Thm_tangent_sampling_deviation_candidates_bddAbove

open MatrixCompletion

/-- Split the positive-rate unit-Frobenius theorem into the finite-dimensional
boundedness of the candidate set and the order-theoretic supremum step. -/
theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (Omega : Finset (Fin n₁ × Fin n₂)) (S : SVD M r) (p epsilon : ℝ) :
    0 < p →
    TangentSamplingDeviationBound Omega S p epsilon →
    ∀ X : Matrix (Fin n₁) (Fin n₂) ℝ,
      tangentProjection S X = X →
      frobeniusNorm X ≤ 1 →
      frobeniusNorm
          (tangentProjection S (samplingProjection Omega X) - p • X) ≤
        epsilon * p := by
  intro hp hDeviation
  exact
    positive_tangent_sampling_deviation_bound_implies_unit_frobenius_concentration_of_bddAbove
      Omega S p epsilon
      (tangent_sampling_deviation_candidates_bddAbove Omega S p)
      hp hDeviation
