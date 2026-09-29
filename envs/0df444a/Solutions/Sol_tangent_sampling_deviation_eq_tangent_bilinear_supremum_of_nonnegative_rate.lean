-- Prove2me | solution 1 for tangent_sampling_deviation_eq_tangent_bilinear_supremum_of_nonnegative_rate
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-25T07:27:51.683936+00:00
-- url     : https://prove2.me/submissions/02d2559a-7af4-45c4-b6ab-3829db43aa6a

import Theorems.Thm_tangent_sampling_deviation_eq_nested_dual_supremum_of_nonnegative_rate
import Theorems.Thm_nested_dual_supremum_eq_tangent_bilinear_supremum

open MatrixCompletion

/-- Source-cited split of the Frobenius-duality step in Appendix 9.1.

Source: Candes-Recht 2008, Appendix 9.1, PDF p. 46, immediately after equation
(9.2), where the paper writes
`Z = sup <X_1, Y(X_2)>`.

The first child dualizes the Frobenius norm in `tangentSamplingDeviation` under
the sampling-rate condition `0 <= p`, producing a nested supremum.  The second
child flattens that nested supremum into the pair supremum defining
`tangentSamplingTangentBilinearDeviation`. -/
theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (Omega : Finset (Fin n₁ × Fin n₂)) (S : SVD M r) (p : ℝ) :
    0 ≤ p →
    tangentSamplingDeviation Omega S p =
      tangentSamplingTangentBilinearDeviation Omega S p := by
  intro hp
  calc
    tangentSamplingDeviation Omega S p =
        tangentSamplingNestedDualDeviation Omega S p :=
      tangent_sampling_deviation_eq_nested_dual_supremum_of_nonnegative_rate
        Omega S p hp
    _ = tangentSamplingTangentBilinearDeviation Omega S p :=
      nested_dual_supremum_eq_tangent_bilinear_supremum Omega S p
