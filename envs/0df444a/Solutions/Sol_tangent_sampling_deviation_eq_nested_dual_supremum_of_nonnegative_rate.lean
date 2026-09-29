-- Prove2me | solution 1 for tangent_sampling_deviation_eq_nested_dual_supremum_of_nonnegative_rate
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-25T07:49:44.036886+00:00
-- url     : https://prove2.me/submissions/51ba2a55-bbb9-41b1-9ada-5fa8bca34c0d

import Theorems.Thm_tangent_sampling_deviation_le_nested_dual_supremum_of_nonnegative_rate
import Theorems.Thm_nested_dual_supremum_le_tangent_sampling_deviation_of_nonnegative_rate

open MatrixCompletion

/-- Split the Frobenius-duality equality into its two order directions.

Source: Candes-Recht 2008, Appendix 9.1, PDF p. 46, immediately after equation
(9.2), where the paper rewrites `Z` as `sup <X_1,Y(X_2)>`.

The first child gives `tangentSamplingDeviation <= nested dual supremum`; the
second gives the reverse inequality from Frobenius Cauchy-Schwarz/dual-norm
control. -/
theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (Omega : Finset (Fin n₁ × Fin n₂)) (S : SVD M r) (p : ℝ) :
    0 ≤ p →
    tangentSamplingDeviation Omega S p =
      tangentSamplingNestedDualDeviation Omega S p := by
  intro hp
  exact le_antisymm
    (tangent_sampling_deviation_le_nested_dual_supremum_of_nonnegative_rate
      Omega S p hp)
    (nested_dual_supremum_le_tangent_sampling_deviation_of_nonnegative_rate
      Omega S p hp)
