-- Prove2me | solution 1 for quadratic_neumann_middle_index_distinct_mean_as_off_diagonal_response
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-07-01T14:21:55.010947+00:00
-- url     : https://prove2.me/submissions/dc9e83d3-8988-4c79-9b37-cfadded6033b

import Definitions.Def_matrix_completion_neumann_middle_response

open MatrixCompletion

/-!
Source: Candes-Recht 2008, Section 6.3, PDF pp. 32--33.

The mean part of the `omega_1 = omega_3 != omega_2` quadratic term equals
`(1-p)` times the middle-index off-diagonal response operator applied to the
centered sampling fluctuation of the rescaled all-ones matrix.  This is a
purely deterministic identity: both sides reduce to the same double sum.
-/
theorem solution
    {n₁ n₂ r : Nat} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (Omega : Finset (Fin n₁ × Fin n₂)) (S : SVD M r) (p : ℝ) :
    quadraticNeumannMiddleIndexDistinctMeanContribution Omega S p =
      (1 - p) •
        quadraticMiddleIndexDistinctOffDiagonalResponse S
          (centeredSamplingFluctuation Omega p (p⁻¹ • onesMatrix n₁ n₂)) := by
  unfold quadraticNeumannMiddleIndexDistinctMeanContribution
    quadraticMiddleIndexDistinctOffDiagonalResponse
  rw [Finset.smul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun w1 _ => ?_)
  rw [Finset.smul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun w2 _ => ?_)
  by_cases hw : w1 = w2
  · simp [hw]
  · simp only [if_neg hw]
    rw [smul_smul, smul_smul]
    congr 1
    have hF :
        centeredSamplingFluctuation Omega p (p⁻¹ • onesMatrix n₁ n₂) w2.1 w2.2 =
          (p⁻¹) ^ 2 * centeredIndicator Omega p w2.1 w2.2 := by
      show (p⁻¹ • (samplingProjection Omega (p⁻¹ • onesMatrix n₁ n₂)
          - p • (p⁻¹ • onesMatrix n₁ n₂))) w2.1 w2.2 = _
      simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      unfold samplingProjection centeredIndicator
      simp only [Matrix.smul_apply, smul_eq_mul, onesMatrix, mul_one]
      by_cases hmem : (w2.1, w2.2) ∈ Omega
      · rw [if_pos hmem, if_pos hmem]; ring
      · rw [if_neg hmem, if_neg hmem]; ring
    rw [hF]
    ring
