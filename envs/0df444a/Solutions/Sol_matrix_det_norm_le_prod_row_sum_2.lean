-- Prove2me | solution 2 for matrix_det_norm_le_prod_row_sum
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-08T04:00:38.347151+00:00
-- url     : https://prove2.me/submissions/d30ccb26-f468-4672-a1a8-2d43368d468f

import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

open scoped BigOperators

theorem solution
    {idx : Type*} [Fintype idx] [DecidableEq idx] (A : Matrix idx idx Complex) :
    norm A.det <= Finset.prod Finset.univ (fun i : idx =>
      Finset.sum Finset.univ (fun j : idx => norm (A i j))) := by
  classical
  let term : (idx → idx) → ℝ := fun f => ∏ i, ‖A i (f i)‖
  let embed : Equiv.Perm idx → (idx → idx) := fun σ => σ
  have hinj : Function.Injective embed := by
    intro σ τ h
    exact Equiv.ext (fun i => congrFun h i)
  calc
    ‖A.det‖ = ‖A.transpose.det‖ := by rw [Matrix.det_transpose]
    _ ≤ ∑ σ : Equiv.Perm idx, term (embed σ) := by
      rw [Matrix.det_apply]
      refine (norm_sum_le _ _).trans_eq ?_
      apply Finset.sum_congr rfl
      intro σ _
      rcases Int.units_eq_one_or σ.sign with hs | hs <;>
        simp [hs, norm_prod, term, embed, Matrix.transpose_apply]
    _ = ∑ f ∈ Finset.univ.image embed, term f := by
      rw [Finset.sum_image (fun σ _ τ _ h => hinj h)]
    _ ≤ ∑ f : idx → idx, term f := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro f _ _
      exact Finset.prod_nonneg (fun i _ => norm_nonneg _)
    _ = ∏ i, ∑ j, ‖A i j‖ := (Fintype.prod_sum (fun i j => ‖A i j‖)).symm

#print axioms solution
