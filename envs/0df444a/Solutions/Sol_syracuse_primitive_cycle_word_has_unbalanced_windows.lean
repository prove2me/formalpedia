-- Prove2me | solution 1 for syracuse_primitive_cycle_word_has_unbalanced_windows
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-24T11:11:41.834841+00:00
-- url     : https://prove2.me/submissions/92eb0676-7f67-4370-b348-1de77afe7799

import Theorems.Thm_syracuse_affine_nondivisibility_of_unit_prefix_rotations
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max

set_option autoImplicit false

namespace SyracuseWindows

/- The take-sum and rotated-index identities are from the accepted Prove2Me
   submission 14e33d46-bd28-46a7-8d29-8a3deb93bad8. -/
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

private def entry (w : List ℕ) (i : ℕ) := w.getD (i % w.length) 0

private def win (w : List ℕ) (i n : ℕ) :=
  ∑ r ∈ Finset.range n, entry w (i+r)

private theorem window_eq (w : List ℕ) (i n : ℕ) (hn : n ≤ w.length) :
    ((w.rotate i).take n).sum = win w i n := by
  rw [take_sum]
  apply Finset.sum_congr rfl
  intro r hr
  rw [rot_getD w i r (lt_of_lt_of_le (Finset.mem_range.mp hr) hn)]
  simp only [entry, Nat.add_comm r i]

private theorem split_window (w : List ℕ) (i m n : ℕ) :
    win w i (m+n) = win w i m + win w (i+m) n := by
  simp only [win, Finset.sum_range_add, Nat.add_assoc]

private theorem window_mod (w : List ℕ) (i n : ℕ) :
    win w (i % w.length) n = win w i n := by
  simp only [win, entry, Nat.mod_add_mod]

private theorem no_cross (w : List ℕ)
    (bal : ∀ i j n, n < w.length → win w i n ≤ win w j n + 1)
    (i j n m : ℕ) (hnm : n ≤ m) (hm : m < w.length)
    (h1 : win w i n < win w j n) (h2 : win w j m < win w i m) : False := by
  have ei := split_window w i n (m-n)
  have ej := split_window w j n (m-n)
  rw [Nat.add_sub_of_le hnm] at ei ej
  have := bal (i+n) (j+n) (m-n) (by omega)
  omega

private theorem ordered (w : List ℕ)
    (bal : ∀ i j n, n < w.length → win w i n ≤ win w j n + 1) (i j : ℕ) :
    (∀ n, n < w.length → win w i n ≤ win w j n) ∨
    (∀ n, n < w.length → win w j n ≤ win w i n) := by
  by_contra! h
  obtain ⟨⟨m, hm, hm'⟩, ⟨n, hn, hn'⟩⟩ := h
  rcases le_total n m with hnm | hmn
  · exact no_cross w bal i j n m hnm hm hn' hm'
  · exact no_cross w bal j i m n hmn hn hm' hn'

private def score (w : List ℕ) (i : ℕ) := ∑ n ∈ Finset.range w.length, win w i n

private theorem score_le_windows (w : List ℕ)
    (bal : ∀ i j n, n < w.length → win w i n ≤ win w j n + 1)
    (i j : ℕ) (hs : score w i ≤ score w j) :
    ∀ n, n < w.length → win w i n ≤ win w j n := by
  rcases ordered w bal i j with h | h
  · exact h
  intro n hn
  by_contra! ht
  have hh : score w j < score w i := Finset.sum_lt_sum
    (fun k hk => h k (Finset.mem_range.mp hk)) ⟨n, Finset.mem_range.mpr hn, ht⟩
  omega

private theorem rotate_of_constant_windows (w : List ℕ) (n : ℕ)
    (hc : ∀ i, win w i n = win w 0 n) : w.rotate n = w := by
  have ep (i : ℕ) : entry w (i+n) = entry w i := by
    have e := split_window w i 1 n
    rw [Nat.add_comm 1 n, split_window w i n 1] at e
    simp only [win, Finset.sum_range_one, Nat.add_zero] at e ⊢
    have h := (hc i).trans (hc (i+1)).symm
    unfold win at h
    omega
  apply List.ext_getElem (by simp)
  intro i hi hi'
  have h := ep i
  have hi'' : (i+n) % w.length < w.length := Nat.mod_lt _ (by omega)
  rw [List.getElem_rotate]
  simpa [entry, Nat.mod_eq_of_lt hi', List.getD_eq_getElem?_getD, hi', hi''] using h

private theorem extreme_pair (w : List ℕ) (hp : 0 < w.length)
    (primitive : ∀ n : ℕ, 0 < n → n < w.length → w.rotate n ≠ w)
    (bal : ∀ i j n, n < w.length → win w i n ≤ win w j n + 1) :
    ∃ i j : ℕ, ∀ n : ℕ, 0 < n → n < w.length →
      ((w.rotate j).take n).sum = ((w.rotate i).take n).sum + 1 := by
  have ne : (Finset.range w.length).Nonempty := ⟨0, Finset.mem_range.mpr hp⟩
  obtain ⟨i, hi, lo⟩ := Finset.exists_min_image _ (score w) ne
  obtain ⟨j, hj, up⟩ := Finset.exists_max_image _ (score w) ne
  refine ⟨i,j,?_⟩
  intro n hpos hn
  rw [window_eq _ _ _ hn.le, window_eq _ _ _ hn.le]
  have lim (x : ℕ) : win w i n ≤ win w x n ∧ win w x n ≤ win w j n := by
    let y := x % w.length
    have hy : y ∈ Finset.range w.length := Finset.mem_range.mpr (Nat.mod_lt _ hp)
    rw [← window_mod w x n]
    exact ⟨score_le_windows w bal i y (lo y hy) n hn,
      score_le_windows w bal y j (up y hy) n hn⟩
  have e := bal j i n hn
  by_contra bad
  apply primitive n hpos hn
  apply rotate_of_constant_windows
  intro x
  have := lim x
  have := lim 0
  omega

end SyracuseWindows

open SyracuseWindows in
theorem solution (w : List ℕ) (hp : 2 ≤ w.length) (hpos : ∀ a ∈ w, 0 < a)
    (hprimitive : ∀ n : ℕ, 0 < n → n < w.length → w.rotate n ≠ w)
    (hgap : 3 ^ w.length < 2 ^ w.sum)
    (hdiv : (2 ^ w.sum - 3 ^ w.length) ∣ syracuseAffineConstant w) :
    ∃ i j n : ℕ, i < w.length ∧ j < w.length ∧ 0 < n ∧ n < w.length ∧
      ((w.rotate i).take n).sum + 2 ≤ ((w.rotate j).take n).sum := by
  by_contra bad
  apply syracuse_affine_nondivisibility_of_unit_prefix_rotations w hp hpos hgap _ hdiv
  apply extreme_pair w (by omega) hprimitive
  intro i j n hn
  by_contra! hh
  have hposn : 0 < n := by
    by_contra! he
    have : n = 0 := by omega
    simp [this, win] at hh
  apply bad
  refine ⟨j % w.length, i % w.length, n, Nat.mod_lt _ (by omega),
    Nat.mod_lt _ (by omega), hposn, hn, ?_⟩
  rw [window_eq _ _ _ hn.le, window_eq _ _ _ hn.le, window_mod, window_mod]
  omega
