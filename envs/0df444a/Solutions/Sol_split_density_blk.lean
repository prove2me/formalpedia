-- Prove2me | solution 1 for split_density_blk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:12:57.771816+00:00
-- url     : https://prove2.me/submissions/e319b66c-a234-4643-aacf-bf4e22e1a89e

module
public import Definitions.Def_ForbiddenMatrix_SmallPatterns
public import Mathlib.Algebra.Group.End
public import Mathlib.Data.Nat.Choose.Basic
public import Definitions.Def_ForbiddenMatrix_Mathlib_Data_ZMod_Basic
public import Mathlib.Combinatorics.Pigeonhole
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Int.Interval
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.Qify
public import Definitions.Def_ForbiddenMatrix_PermutationPatterns
public import Theorems.Thm_permPattern_one
public import Theorems.Thm_permPattern_refl
public import Theorems.Thm_den_submatrix_eq_sum_blk_den
public import Theorems.Thm_Fin_natCast_val_eq_zmodFinEquiv
public import Theorems.Thm_card_interval
public import Theorems.Thm_card_rectPtSet
public import Theorems.Thm_card_rectPtsetSubsetMatrix
public import Theorems.Thm_contains_of_isEmpty
public import Theorems.Thm_ex_identityPattern_two
public import Theorems.Thm_ex_zero
public import Theorems.Thm_split_density
attribute [local simp] Fin.natCast_val_eq_zmodFinEquiv
attribute [local simp] card_rectPtSet
attribute [local simp] card_rectPtsetSubsetMatrix
attribute [local simp] contains_of_isEmpty
attribute [local simp] ex_identityPattern_two
attribute [local simp] ex_zero


attribute [local simp] permPattern_one
attribute [local simp] permPattern_refl
section
@[expose] public section
open Finset Set OrderDual Equiv
variable {k n q : ℕ}
@[simp] private lemma le_mul_div_add_one {n q : ℕ} (p : Fin n) (h : 0 < q) : p < q * (p / q + 1) := by
  rw [Nat.mul_comm]
  exact Nat.lt_mul_of_div_lt (Nat.lt_add_one _) h
@[simp] private lemma card_intervalq (n q i : ℕ) (hn : 0 < n) (hq : q ∣ n) (h : i < n / q) :
    #{a : Fin n | ↑a ∈ Finset.Ico (q * ↑i) (q * (↑i + 1))} = q := by
  have hy : q * (i + 1) ≤ n := by
    observe h1 : q * (n / q - 1) = q * (n / q) - q
    observe h2 : q * (n / q) = n
    observe : i ≤ n / q - 1
    observe h3 : q * i ≤ q * (n / q - 1)
    calc
          q * (i+1)
      _ = q * i + q := rfl
      _ ≤ q * (n / q -1) + q := Nat.add_le_add_right h3 q
      _ = (q * (n / q) - q) + q := Nat.add_right_cancel_iff.mpr h1
      _ = n := by
        rw [h2]
        have : n - q + q = n + q - q := by
          have := Nat.le_of_dvd hn hq
          lia
        rw [this]
        exact Eq.symm (Nat.eq_sub_of_add_eq rfl)
  calc
     #{a : Fin n | ↑a ∈ Finset.Ico (q * ↑i) (q * (↑i + 1))}
      = #(.Ico (q * ↑i) (q * (↑i + 1))) := card_interval (q * i) (q * (i + 1)) hy
     _ = (q * (↑i + 1)) - (q * ↑i) := Nat.card_Ico (q * i) (q * (i + 1))
     _ = q := Nat.sub_eq_of_eq_add' rfl
@[simp] private lemma card_rectPtsetq (n q i j : ℕ) (hq : q ∣ n) (h : i < n / q ∧ j < n / q) :
    #(rectPtsetq n q i j) = q * q := by
  simp only [rectPtsetq]
  convert card_rectPtSet n (q * i) (q * (i+1)) (q * j) (q * (j+1)) _
  · exact Nat.eq_sub_of_add_eq' rfl
  · exact Nat.eq_sub_of_add_eq' rfl
  obtain ⟨hi, hj⟩ := h
  constructor
  · calc
      q * (i+1) ≤ q * (n / q) := Nat.mul_le_mul_left q hi
      _     = n    := Nat.mul_div_cancel' hq
  · calc
      q * (j+1) ≤ q * (n / q) := Nat.mul_le_mul_left q hj
      _     = n    := Nat.mul_div_cancel' hq
set_option backward.isDefEq.respectTransparency false in
@[simp] private lemma card_rectPtsetqMatrix (M : Fin n → Fin n → Prop) (hq : q ∣ n) (i j : ℕ)
    (h : i < n / q ∧ j < n / q) : #(rectPtsetqMatrix M q i j) ≤ q * q := by
  calc
    #(rectPtsetqMatrix M q i j)
    _ ≤ #(rectPtsetq n q i j) := ?_
    _ = q * q := card_rectPtsetq n q i j hq h
  -- proof of the claim
  refine Finset.card_le_card ?_
  simp only [rectPtsetqMatrix, rectPtsetq, Prod.mk.eta]
  intro p h
  simp only [mem_filter, Finset.mem_univ, true_and] at h
  exact h.2
@[simp] private lemma p_to_pq {p : Fin n × Fin n} (hq : q ≠ 0) :
    p ∈ rectPtset n (q * (p.1 / q)) (q * (p.1 / q + 1)) (q * (p.2 / q)) (q * (p.2 / q + 1)) := by
  simp only [rectPtset, Finset.mem_Ico, mem_product, mem_filter, Finset.mem_univ, true_and]
  constructor <;> exact ⟨Nat.mul_div_le .., le_mul_div_add_one _ <| by lia⟩
end
end

set_option autoImplicit true
@[expose] public section
public section
open Finset Set OrderDual Equiv
variable {k n q : ℕ}
open scoped Classical
theorem _root_.solution {n q : ℕ} (hqn : q ∣ n) (M : Fin n → Fin n → Prop)
    (f1 f2 : Fin (n / q) → Fin (n / q) → Prop) :
    let Q := Fin (n / q) × Fin (n / q)
    let f3 := fun i j ↦ (¬ f1 i j) ∧ ¬ (f2 i j)
    let B := blkMatrix M q
    let B1 (i j : Fin (n / q)) : Prop := B i j ∧ f1 i j
    let B2 (i j : Fin (n / q)) : Prop := B i j ∧ f2 i j
    let N  (i j : Fin (n / q)) : Prop := B i j ∧ f3 i j
    density M ≤ ∑ ij : Q with B1 ij.1 ij.2, blk_den M ij.1 ij.2 +
                ∑ ij : Q with B2 ij.1 ij.2, blk_den M ij.1 ij.2 +
                ∑ ij : Q with N ij.1 ij.2, blk_den M ij.1 ij.2 := by
  obtain rfl | hn := eq_zero_or_neZero n
  · simp [density, blkMatrix]
  obtain rfl | hq := eq_or_ne q 0
  · simp [NeZero.ne n] at hqn
  extract_lets Q f3 B B1 B2 N
  let fq (x : Fin n) : Fin (n / q) := ⟨x / q, Nat.div_lt_div_of_lt_of_dvd hqn x.isLt⟩
  let P1 (i j : Fin n) : Prop := B1 (fq i) (fq j)
  let P2 (i j : Fin n) : Prop := B2 (fq i) (fq j)
  let P3 (i j : Fin n) : Prop := N (fq i) (fq j)
  let M1 (i j : Fin n) : Prop := M i j ∧ P1 i j
  let M2 (i j : Fin n) : Prop := M i j ∧ P2 i j
  let M3 (i j : Fin n) : Prop := M i j ∧ P3 i j
  suffices density M ≤ density M1 + density M2 + density M3 from by
    have : density M1 = ∑ ⟨i, j⟩ : Q with B1 i j, blk_den M i j := by
      convert den_submatrix_eq_sum_blk_den M hqn f1
    have : density M2 = ∑ ⟨i, j⟩ : Q with B2 i j, blk_den M i j := by
      convert den_submatrix_eq_sum_blk_den M hqn f2
    have : density M3 = ∑ ⟨i, j⟩ : Q with N i j , blk_den M i j := by
      convert den_submatrix_eq_sum_blk_den M hqn f3
    lia
  let M1' (i j : Fin n) : Prop := M i j ∧ ¬ P1 i j
  let M2' (i j : Fin n) : Prop := M1' i j ∧ P2 i j
  let M3' (i j : Fin n) : Prop := M1' i j ∧ ¬P2 i j
  have h2 : density M1' = density M2' + density M3' := by exact split_density M1' P2
  have h3 : density M3' = density M3 := by
    suffices M3' = M3 by aesop
    ext i j
    simp only [M3', M1']
    rw [and_assoc]
    simp only [and_congr_right_iff, M3]
    intro Mij
    simp only [not_and, P1, B1, P2, B2, P3, N, f3]
    suffices B (fq i) (fq j) by tauto
    simp only [blkMatrix, rectPtsetq, Prod.exists, B, fq]
    exact ⟨i, j, Mij, p_to_pq (p := (i, j)) hq⟩
  have : density M2' ≤ density M2 := by
    simp only [density, M2', M1', M2]
    apply Finset.card_le_card
    intro p a
    simp_all
  calc
    density M = density M1 + density M1' := split_density M P1
    _        = density M1 + density M2' + density M3' := by lia
    _         ≤ density M1 + density M2' + density M3 := by lia
    _         ≤ density M1 + density M2 + density M3 := by lia
