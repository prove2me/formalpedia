-- Prove2me | solution 1 for tangent_bilinear_supremum_eq_talagrand_supremum
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-25T06:32:03.556511+00:00
-- url     : https://prove2.me/submissions/3c48b3b7-c525-4262-ac24-592e7513b76e

import Theorems.Thm_tangent_bilinear_supremum_eq_coordinate_tangent_supremum
import Theorems.Thm_coordinate_tangent_supremum_eq_talagrand_supremum

open MatrixCompletion

/-- Source-cited split of the Appendix 9.1 coordinate representation.

Source: Candes-Recht 2008, Appendix 9.1, PDF p. 46, immediately after equation
(9.2), where the tangent sampling deviation is written as the coordinate
supremum over `X_1` and `X_2`.

The first child expands the tangent-restricted bilinear form in the coordinate
basis.  The second child removes the tangent restriction on the second test
matrix, using that the displayed coefficients only see `P_T X_2`. -/
theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (Omega : Finset (Fin n₁ × Fin n₂)) (S : SVD M r) (p : ℝ) :
    tangentSamplingTangentBilinearDeviation Omega S p =
      tangentSamplingTalagrandSupremumDeviation Omega S p := by
  calc
    tangentSamplingTangentBilinearDeviation Omega S p =
        tangentSamplingCoordinateTangentSupremumDeviation Omega S p :=
      tangent_bilinear_supremum_eq_coordinate_tangent_supremum Omega S p
    _ = tangentSamplingTalagrandSupremumDeviation Omega S p :=
      coordinate_tangent_supremum_eq_talagrand_supremum Omega S p
