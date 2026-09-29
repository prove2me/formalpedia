-- Prove2me | solution 1 for positive_tangent_sampling_deviation_bound_implies_concentration
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T06:26:59.867604+00:00
-- url     : https://prove2.me/submissions/f91daf33-94b9-497c-8b7b-10134b95b252

import Theorems.Thm_positive_tangent_sampling_deviation_bound_implies_unit_frobenius_concentration
import Theorems.Thm_unit_frobenius_tangent_concentration_extends_by_homogeneity

open MatrixCompletion

/-- Convert the positive-rate normalized deviation bound into pointwise tangent
concentration by first proving the unit-Frobenius estimate and then rescaling. -/
theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (Omega : Finset (Fin n₁ × Fin n₂)) (S : SVD M r) (p epsilon : ℝ) :
    0 < p →
    TangentSamplingDeviationBound Omega S p epsilon →
    TangentSamplingConcentration Omega S p epsilon := by
  intro hp hDeviation
  have hUnit :=
    positive_tangent_sampling_deviation_bound_implies_unit_frobenius_concentration
      Omega S p epsilon hp hDeviation
  exact unit_frobenius_tangent_concentration_extends_by_homogeneity
    Omega S p epsilon (le_of_lt hp) hUnit
