-- Prove2me | solution 1 for matrix_gram_det_le_prod_row_sq
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-07T20:40:28.222022+00:00
-- url     : https://prove2.me/submissions/1725b7cb-26c3-45fa-a5dc-40a6e1c3b311
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_complex_posSemidef_det_le_prod_diag_re
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
open scoped ComplexOrder

theorem solution {idx : Type*} [Fintype idx] [DecidableEq idx]
    (A : Matrix idx idx Complex) :
    (A * Matrix.conjTranspose A).det.re <= Finset.prod Finset.univ (fun i : idx =>
      Finset.sum Finset.univ (fun j : idx => norm (A i j) ^ 2)) := by
  classical
  have hpsd : (A * Matrix.conjTranspose A).PosSemidef :=
    Matrix.posSemidef_self_mul_conjTranspose A
  have hdiag (i : idx) :
      ((A * Matrix.conjTranspose A) i i).re =
        Finset.sum Finset.univ (fun j : idx => norm (A i j) ^ 2) := by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def, Complex.mul_conj']
    rw [Complex.re_sum (s := Finset.univ)]
    simp_rw [(Complex.ofReal_pow _ _).symm, Complex.ofReal_re]
  have h := complex_posSemidef_det_le_prod_diag_re (A * Matrix.conjTranspose A) hpsd
  calc
    (A * Matrix.conjTranspose A).det.re <=
        Finset.prod Finset.univ (fun i : idx => ((A * Matrix.conjTranspose A) i i).re) := h
    _ = Finset.prod Finset.univ (fun i : idx =>
        Finset.sum Finset.univ (fun j : idx => norm (A i j) ^ 2)) := by
      apply Finset.prod_congr rfl
      intro i hi
      exact hdiag i


