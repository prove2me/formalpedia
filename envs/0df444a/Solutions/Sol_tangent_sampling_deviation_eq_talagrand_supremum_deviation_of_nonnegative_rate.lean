-- Prove2me | solution 1 for tangent_sampling_deviation_eq_talagrand_supremum_deviation_of_nonnegative_rate
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-25T06:20:28.550291+00:00
-- url     : https://prove2.me/submissions/2e4c8080-f536-4bf7-829a-540d6064586c

import Theorems.Thm_tangent_sampling_deviation_eq_tangent_bilinear_supremum_of_nonnegative_rate
import Theorems.Thm_tangent_bilinear_supremum_eq_talagrand_supremum

open MatrixCompletion

/-- Source-cited representation split for Appendix 9.1, with the sampling-rate
side condition retained.

Source: Candes-Recht 2008, Appendix 9.1, PDF p. 46, immediately after equation
(9.2), where the random variable
`Z = p^{-1} ||P_T P_Omega P_T - p P_T||` is rewritten as a bilinear supremum
over `X_1` and `X_2`.  The paper applies this with
`p = m/(n_1 n_2) >= 0`; the corrected statement keeps that hypothesis.

The first imported child is the Frobenius-duality step under `0 <= p`.  The
second imported child is the coordinate expansion of the tangent-restricted
bilinear form and the removal of the tangent restriction from the second test
matrix. -/
theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (p : ℝ) :
    0 ≤ p →
    (fun Omega : Finset (Fin n₁ × Fin n₂) =>
      tangentSamplingDeviation Omega S p) =
    (fun Omega : Finset (Fin n₁ × Fin n₂) =>
      tangentSamplingTalagrandSupremumDeviation Omega S p) := by
  intro hp
  funext Omega
  calc
    tangentSamplingDeviation Omega S p =
        tangentSamplingTangentBilinearDeviation Omega S p :=
      tangent_sampling_deviation_eq_tangent_bilinear_supremum_of_nonnegative_rate
        Omega S p hp
    _ = tangentSamplingTalagrandSupremumDeviation Omega S p :=
      tangent_bilinear_supremum_eq_talagrand_supremum Omega S p
