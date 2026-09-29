-- Prove2me | solution 1 for quadratic_neumann_all_distinct_inner_base_norms_le_linear_offdiag_base
-- status  : ACCEPTED   (prove)
-- author  : @Minghui
-- created : 2026-06-26T21:47:01.949897+00:00
-- url     : https://prove2.me/submissions/c98620dd-eae0-4234-8127-c84f139b49a3

import Definitions.Def_linear_neumann_offdiag_bernstein

open MatrixCompletion
open scoped Classical BigOperators

namespace ProveAllDistinctInnerBaseZeroing

private theorem quadraticAllDistinctInnerBase_pointwise_abs_le_linear
    {n₁ n₂ r : Nat} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (w1 w2 : Fin n₁ × Fin n₂) :
    ∀ i j,
      |quadraticAllDistinctInnerBaseMatrix S w1 w2 i j| ≤
        |linearNeumannOffDiagonalCoefficientBaseMatrix S w2 i j| := by
  intro i j
  unfold quadraticAllDistinctInnerBaseMatrix
  unfold linearNeumannOffDiagonalCoefficientBaseMatrix
  by_cases h2 : (i, j) = w2
  · simp [h2]
  · by_cases h1 : (i, j) = w1
    · simp [h1]
    · simp [h1, h2]

private theorem quadraticAllDistinctInnerBase_frobeniusSq_le_linear
    {n₁ n₂ r : Nat} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (w1 w2 : Fin n₁ × Fin n₂) :
    frobeniusNormSq (quadraticAllDistinctInnerBaseMatrix S w1 w2) ≤
      frobeniusNormSq (linearNeumannOffDiagonalCoefficientBaseMatrix S w2) := by
  unfold frobeniusNormSq
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  unfold quadraticAllDistinctInnerBaseMatrix
  unfold linearNeumannOffDiagonalCoefficientBaseMatrix
  by_cases h2 : (i, j) = w2
  · simp [h2]
  · by_cases h1 : (i, j) = w1
    · have h12 : w1 ≠ w2 := by
        intro h
        exact h2 (by simp [h1, h])
      simp [h1, h12, sq_nonneg]
    · simp [h1, h2]

end ProveAllDistinctInnerBaseZeroing

open ProveAllDistinctInnerBaseZeroing

theorem solution
    {n₁ n₂ r : Nat} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (w1 w2 : Fin n₁ × Fin n₂) :
    entrySupNorm (quadraticAllDistinctInnerBaseMatrix S w1 w2) ≤
        entrySupNorm (linearNeumannOffDiagonalCoefficientBaseMatrix S w2) ∧
      frobeniusNorm (quadraticAllDistinctInnerBaseMatrix S w1 w2) ≤
        frobeniusNorm (linearNeumannOffDiagonalCoefficientBaseMatrix S w2) := by
  constructor
  · unfold entrySupNorm
    apply ciSup_mono
    · exact Finite.bddAbove_range
        (fun i : Fin n₁ => ⨆ j : Fin n₂,
          |linearNeumannOffDiagonalCoefficientBaseMatrix S w2 i j|)
    intro i
    apply ciSup_mono
    · exact Finite.bddAbove_range
        (fun j : Fin n₂ => |linearNeumannOffDiagonalCoefficientBaseMatrix S w2 i j|)
    intro j
    exact quadraticAllDistinctInnerBase_pointwise_abs_le_linear S w1 w2 i j
  · unfold frobeniusNorm
    exact Real.sqrt_le_sqrt
      (quadraticAllDistinctInnerBase_frobeniusSq_le_linear S w1 w2)
