-- Prove2me | solution 1 for syracuse_affine_constant_some_rotation_le_mechanical_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T03:30:37.984349+00:00
-- url     : https://prove2.me/submissions/14e33d46-bd28-46a7-8d29-8a3deb93bad8

import Mathlib
import Definitions.Def_syracuseOffsetMod

set_option autoImplicit false

open scoped BigOperators

namespace P695ac23a

lemma C_eq (w : List ℕ) : syracuseAffineConstant w =
    ∑ j ∈ Finset.range w.length, 3 ^ (w.length - 1 - j) * 2 ^ (w.take j).sum := by
  induction w with
  | nil => simp [syracuseAffineConstant]
  | cons a as ih =>
    rw [syracuseAffineConstant, ih, List.length_cons, Finset.sum_range_succ', Finset.mul_sum,
      add_comm]
    congr 1
    · apply Finset.sum_congr rfl
      intro j _
      rw [List.take_succ_cons, List.sum_cons, pow_add]
      have : as.length + 1 - 1 - (j + 1) = as.length - 1 - j := by omega
      rw [this]; ring
    · simp

lemma take_sum (l : List ℕ) (j : ℕ) :
    (l.take j).sum = ∑ i ∈ Finset.range j, l.getD i 0 := by
  induction l generalizing j with
  | nil => simp
  | cons a l ih =>
    cases j with
    | zero => simp
    | succ j =>
      rw [List.take_succ_cons, List.sum_cons, ih, Finset.sum_range_succ']
      simp [add_comm]

lemma rot_getD (w : List ℕ) (d i : ℕ) (hi : i < w.length) :
    (w.rotate d).getD i 0 = w.getD ((i + d) % w.length) 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_rotate hi]

theorem main (w : List ℕ) (hp : 0 < w.length) :
    ∃ d : ℕ, d < w.length ∧
      syracuseAffineConstant (w.rotate d) ≤
        ∑ j ∈ Finset.range w.length,
          (3 ^ (w.length - 1 - j) * 2 ^ ((w.sum * j) / w.length)) := by
  let a : ℕ → ℕ := fun i => w.getD (i % w.length) 0
  let P : ℕ → ℕ := fun n => ∑ i ∈ Finset.range n, a i
  have hPp : P w.length = w.sum := by
    have h1 : P w.length = ∑ i ∈ Finset.range w.length, w.getD i 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [a, Nat.mod_eq_of_lt (Finset.mem_range.mp hi)]
    rw [h1, ← take_sum, List.take_length]
  have hper : ∀ n, P (n + w.length) = P n + w.sum := by
    intro n
    induction n with
    | zero => simp only [zero_add, hPp, P, Finset.range_zero, Finset.sum_empty]
    | succ n ih =>
      have e1 : P (n + 1 + w.length) = P (n + w.length) + a (n + w.length) := by
        rw [show n + 1 + w.length = n + w.length + 1 by omega]
        exact Finset.sum_range_succ _ _
      have e2 : P (n + 1) = P n + a n := Finset.sum_range_succ _ _
      have e3 : a (n + w.length) = a n := by simp only [a, Nat.add_mod_right]
      rw [e1, e2, e3, ih]; ring
  let f : ℕ → ℤ := fun n => (w.length : ℤ) * (P n : ℤ) - (w.sum : ℤ) * (n : ℤ)
  obtain ⟨d, hd, hmax⟩ := Finset.exists_max_image (Finset.range w.length) f
    ⟨0, Finset.mem_range.mpr hp⟩
  have hd' : d < w.length := Finset.mem_range.mp hd
  have hT : ∀ j, j ≤ w.length → P d + ((w.rotate d).take j).sum = P (d + j) := by
    intro j hj
    rw [take_sum]
    simp only [P]
    rw [Finset.sum_range_add]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i < w.length := lt_of_lt_of_le (Finset.mem_range.mp hi) hj
    rw [rot_getD w d i hi']
    simp only [a, add_comm i d]
  have key : ∀ j, j < w.length →
      ((w.rotate d).take j).sum * w.length ≤ w.sum * j := by
    intro j hj
    have hTj := hT j hj.le
    by_cases hc : d + j < w.length
    · have h1 := hmax (d + j) (Finset.mem_range.mpr hc)
      simp only [f] at h1
      have h2 : ((P d : ℕ) : ℤ) + (((w.rotate d).take j).sum : ℤ) = (P (d + j) : ℤ) := by
        exact_mod_cast hTj
      rw [← h2] at h1
      rw [Nat.cast_add] at h1
      have : ((((w.rotate d).take j).sum * w.length : ℕ) : ℤ) ≤ ((w.sum * j : ℕ) : ℤ) := by
        rw [Nat.cast_mul, Nat.cast_mul]
        nlinarith
      exact_mod_cast this
    · push Not at hc
      set e := d + j - w.length with he
      have he' : e + w.length = d + j := by omega
      have helt : e < w.length := by omega
      have h1 := hmax e (Finset.mem_range.mpr helt)
      simp only [f] at h1
      have h3 : P (d + j) = P e + w.sum := by rw [← he', hper]
      have h2 : ((P d : ℕ) : ℤ) + (((w.rotate d).take j).sum : ℤ) = (P e : ℤ) + (w.sum : ℤ) := by
        have h4 := hTj
        rw [h3] at h4
        exact_mod_cast h4
      have he'' : (e : ℤ) + (w.length : ℤ) = (d : ℤ) + (j : ℤ) := by exact_mod_cast he'
      have : ((((w.rotate d).take j).sum * w.length : ℕ) : ℤ) ≤ ((w.sum * j : ℕ) : ℤ) := by
        rw [Nat.cast_mul, Nat.cast_mul]
        have hj' : (j : ℤ) = (e : ℤ) + (w.length : ℤ) - (d : ℤ) := by linarith
        rw [hj']
        nlinarith
      exact_mod_cast this
  refine ⟨d, hd', ?_⟩
  rw [C_eq, List.length_rotate]
  apply Finset.sum_le_sum
  intro j hj
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_right (by norm_num)
  rw [Nat.le_div_iff_mul_le hp]
  exact key j (Finset.mem_range.mp hj)

end P695ac23a

theorem solution (w : List ℕ) (hp : 0 < w.length) :
    ∃ d : ℕ, d < w.length ∧
      syracuseAffineConstant (w.rotate d) ≤
        ∑ j ∈ Finset.range w.length,
          (3 ^ (w.length - 1 - j) * 2 ^ ((w.sum * j) / w.length)) := by
  exact P695ac23a.main w hp
