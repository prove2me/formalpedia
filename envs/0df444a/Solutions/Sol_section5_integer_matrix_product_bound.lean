-- Prove2me | solution 1 for section5_integer_matrix_product_bound
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:55:24.866259+00:00
-- url     : https://prove2.me/submissions/9512f9ef-9b19-426f-9626-8647312da608

import Definitions.Def_Section5Verified_Section5IntegerMatrixBounds
import Mathlib
set_option autoImplicit false
theorem solution {n : ℕ}
    (A B : Section5IntegerMatrix n) (a b : ℤ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : A.Bounded a) (hB : B.Bounded b) : (A.mul B).Bounded (2*n*a*b) := by
  have hsum (X Y : Matrix (Fin n) (Fin n) ℤ)
      (hX : ∀ i j, |X i j| ≤ a) (hY : ∀ i j, |Y i j| ≤ b) (i j : Fin n) :
      |(X*Y) i j| ≤ n*a*b := by
    rw [Matrix.mul_apply]
    calc
      _ ≤ ∑ k : Fin n,|X i k*Y k j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k : Fin n,a*b := by
        apply Finset.sum_le_sum
        intro k hk
        rw [abs_mul]
        exact mul_le_mul (hX i k) (hY k j) (abs_nonneg _) ha
      _ = _ := by simp; ring
  constructor
  · intro i j
    change |(A.re*B.re) i j-(A.im*B.im) i j| ≤ _
    exact (abs_sub _ _).trans ((add_le_add (hsum _ _ hA.1 hB.1 i j)
      (hsum _ _ hA.2 hB.2 i j)).trans_eq (by ring))
  · intro i j
    change |(A.re*B.im) i j+(A.im*B.re) i j| ≤ _
    exact (abs_add_le _ _).trans ((add_le_add (hsum _ _ hA.1 hB.2 i j)
      (hsum _ _ hA.2 hB.1 i j)).trans_eq (by ring))
