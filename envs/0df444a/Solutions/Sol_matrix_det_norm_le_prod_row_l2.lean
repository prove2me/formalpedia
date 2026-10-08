-- Prove2me | solution 1 for matrix_det_norm_le_prod_row_l2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-07T20:16:13.331337+00:00
-- url     : https://prove2.me/submissions/0479df67-2038-4d61-9e38-b08a03242162
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_matrix_gram_det_le_prod_row_sq
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.Real.Sqrt

theorem solution {idx : Type*} [Fintype idx] [DecidableEq idx]
    (A : Matrix idx idx Complex) :
    norm A.det <= Finset.prod Finset.univ (fun i : idx =>
      Real.sqrt (Finset.sum Finset.univ (fun j : idx => norm (A i j) ^ 2))) := by
  classical
  have hgram := matrix_gram_det_le_prod_row_sq A
  have hdet : (A * Matrix.conjTranspose A).det.re = norm A.det ^ 2 := by
    rw [Matrix.det_mul, Matrix.det_conjTranspose]
    simp only [Complex.star_def, Complex.mul_conj']
    rw [← Complex.ofReal_pow, Complex.ofReal_re]
  have hprod : (norm A.det) ^ 2 <=
      (Finset.prod Finset.univ (fun i : idx =>
        Real.sqrt (Finset.sum Finset.univ (fun j : idx => norm (A i j) ^ 2)))) ^ 2 := by
    rw [← hdet]
    calc
      (A * Matrix.conjTranspose A).det.re <= Finset.prod Finset.univ (fun i : idx =>
          Finset.sum Finset.univ (fun j : idx => norm (A i j) ^ 2)) := hgram
      _ = Finset.prod Finset.univ (fun i : idx =>
          Real.sqrt (Finset.sum Finset.univ (fun j : idx => norm (A i j) ^ 2)) *
          Real.sqrt (Finset.sum Finset.univ (fun j : idx => norm (A i j) ^ 2))) := by
        apply Finset.prod_congr rfl
        intro i hi
        have hs : 0 <= Finset.sum Finset.univ (fun j : idx => norm (A i j) ^ 2) :=
          Finset.sum_nonneg fun j hj => sq_nonneg (norm (A i j))
        calc
          Finset.sum Finset.univ (fun j : idx => norm (A i j) ^ 2) =
              Real.sqrt (Finset.sum Finset.univ (fun j : idx => norm (A i j) ^ 2)) ^ 2 :=
                (Real.sq_sqrt hs).symm
          _ = Real.sqrt (Finset.sum Finset.univ (fun j : idx => norm (A i j) ^ 2)) *
              Real.sqrt (Finset.sum Finset.univ (fun j : idx => norm (A i j) ^ 2)) := by ring
      _ = (Finset.prod Finset.univ (fun i : idx =>
            Real.sqrt (Finset.sum Finset.univ (fun j : idx => norm (A i j) ^ 2))) ^ 2) := by
        rw [Finset.prod_mul_distrib]
        ring
  have hright : 0 <= Finset.prod Finset.univ (fun i : idx =>
      Real.sqrt (Finset.sum Finset.univ (fun j : idx => norm (A i j) ^ 2))) := by
    apply Finset.prod_nonneg
    intro i hi
    exact Real.sqrt_nonneg _
  nlinarith [norm_nonneg A.det]