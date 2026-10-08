-- Prove2me | solution 1 for matrix_det_norm_le_prod_row_sum
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-07T20:06:45.953524+00:00
-- url     : https://prove2.me/submissions/d30c54b5-dd34-47b2-a8ef-b66778263150
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_matrix_det_norm_le_prod_row_l2

theorem solution
    {idx : Type*} [Fintype idx] [DecidableEq idx] (A : Matrix idx idx Complex) :
    norm A.det <= Finset.prod Finset.univ (fun i : idx =>
      Finset.sum Finset.univ (fun j : idx => norm (A i j))) := by
  classical
  calc
    norm A.det <= Finset.prod Finset.univ (fun i : idx =>
        Real.sqrt (Finset.sum Finset.univ (fun j : idx => norm (A i j) ^ 2))) :=
      matrix_det_norm_le_prod_row_l2 A
    _ <= Finset.prod Finset.univ (fun i : idx =>
        Finset.sum Finset.univ (fun j : idx => norm (A i j))) := by
      apply Finset.prod_le_prod
      · intro i hi
        positivity
      · intro i hi
        apply Real.sqrt_le_iff.mpr
        constructor
        · exact Finset.sum_nonneg fun j hj => norm_nonneg _
        · simpa using
            (Finset.sum_sq_le_sq_sum_of_nonneg
              (s := Finset.univ) (fun j hj => norm_nonneg (A i j)))