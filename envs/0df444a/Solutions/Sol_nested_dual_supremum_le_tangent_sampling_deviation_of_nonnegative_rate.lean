-- Prove2me | solution 1 for nested_dual_supremum_le_tangent_sampling_deviation_of_nonnegative_rate
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-25T08:01:25.48282+00:00
-- url     : https://prove2.me/submissions/52140d9a-6e31-4ad7-887c-c2358caee529

import Definitions.Def_matrix_completion_talagrand_nested_dual
import Theorems.Thm_tangent_sampling_deviation_candidates_bddAbove
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

open MatrixCompletion
open scoped Classical BigOperators

private theorem matrix_inner_le_frobenius_mul {n₁ n₂ : ℕ}
    (X Y : Matrix (Fin n₁) (Fin n₂) ℝ) :
    matrixInner X Y ≤ frobeniusNorm X * frobeniusNorm Y := by
  have hsq : (matrixInner X Y) ^ 2 ≤ frobeniusNormSq X * frobeniusNormSq Y := by
    unfold matrixInner frobeniusNormSq
    have h := Finset.sum_mul_sq_le_sq_mul_sq
      (Finset.univ : Finset (Fin n₁ × Fin n₂))
      (fun p : Fin n₁ × Fin n₂ => X p.1 p.2)
      (fun p : Fin n₁ × Fin n₂ => Y p.1 p.2)
    rw [Fintype.sum_prod_type] at h
    rw [Fintype.sum_prod_type] at h
    rw [Fintype.sum_prod_type] at h
    simpa using h
  have hx0 : 0 ≤ frobeniusNormSq X := by
    unfold frobeniusNormSq
    positivity
  have habs :
      |matrixInner X Y| ≤ Real.sqrt (frobeniusNormSq X * frobeniusNormSq Y) := by
    rw [← Real.sqrt_sq_eq_abs (matrixInner X Y)]
    exact Real.sqrt_le_sqrt hsq
  have hsqrt :
      Real.sqrt (frobeniusNormSq X * frobeniusNormSq Y) =
        frobeniusNorm X * frobeniusNorm Y := by
    unfold frobeniusNorm
    rw [Real.sqrt_mul hx0]
  exact le_trans (le_abs_self (matrixInner X Y)) (by simpa [hsqrt] using habs)

private theorem scaled_matrix_inner_le_scaled_frobenius_of_unit {n₁ n₂ : ℕ}
    (X Y : Matrix (Fin n₁) (Fin n₂) ℝ) (p : ℝ) :
    0 ≤ p →
    frobeniusNorm X ≤ 1 →
    p⁻¹ * matrixInner X Y ≤ p⁻¹ * frobeniusNorm Y := by
  intro hp hX
  have hinv : 0 ≤ p⁻¹ := inv_nonneg.mpr hp
  have hnonnegY : 0 ≤ frobeniusNorm Y := by
    unfold frobeniusNorm
    positivity
  have hinner : matrixInner X Y ≤ frobeniusNorm Y := by
    calc
      matrixInner X Y ≤ frobeniusNorm X * frobeniusNorm Y :=
        matrix_inner_le_frobenius_mul X Y
      _ ≤ 1 * frobeniusNorm Y := mul_le_mul_of_nonneg_right hX hnonnegY
      _ = frobeniusNorm Y := one_mul _
  exact mul_le_mul_of_nonneg_left hinner hinv

theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (Omega : Finset (Fin n₁ × Fin n₂)) (S : SVD M r) (p : ℝ) :
    0 ≤ p →
    tangentSamplingNestedDualDeviation Omega S p ≤
      tangentSamplingDeviation Omega S p := by
  intro hp
  unfold tangentSamplingNestedDualDeviation tangentSamplingDeviation
  refine csSup_le ?outer_nonempty ?outer_le
  · refine ⟨sSup {w : ℝ | ∃ X1 : Matrix (Fin n₁) (Fin n₂) ℝ,
      frobeniusNorm X1 ≤ 1 ∧
        w = p⁻¹ * matrixInner X1
          (tangentProjection S (samplingProjection Omega 0) -
            p • (0 : Matrix (Fin n₁) (Fin n₂) ℝ))}, ?_⟩
    refine ⟨0, ?_, ?_, rfl⟩
    · ext i j
      simp [tangentProjection, leftSingularProjection, rightSingularProjection,
        twoSidedSingularProjection]
    · unfold frobeniusNorm frobeniusNormSq
      simp
  · intro b hb
    rcases hb with ⟨X2, hT, hX2, rfl⟩
    refine csSup_le ?inner_nonempty ?inner_le
    · refine ⟨0, ?_⟩
      refine ⟨0, ?_, ?_⟩
      · unfold frobeniusNorm frobeniusNormSq
        simp
      · simp [matrixInner]
    · intro w hw
      rcases hw with ⟨X1, hX1, rfl⟩
      have hscaled :=
        scaled_matrix_inner_le_scaled_frobenius_of_unit X1
          (tangentProjection S (samplingProjection Omega X2) - p • X2) p hp hX1
      refine le_trans hscaled ?_
      refine le_csSup (tangent_sampling_deviation_candidates_bddAbove Omega S p) ?_
      exact ⟨X2, hT, hX2, rfl⟩
