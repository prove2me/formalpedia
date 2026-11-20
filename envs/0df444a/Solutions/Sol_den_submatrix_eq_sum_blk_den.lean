-- Prove2me | solution 1 for den_submatrix_eq_sum_blk_den
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:12:02.873193+00:00
-- url     : https://prove2.me/submissions/c2652b9b-4f93-4a20-9066-092015b83313

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
public import Theorems.Thm_den_eq_sum_blk_den
public import Theorems.Thm_Fin_natCast_val_eq_zmodFinEquiv
public import Theorems.Thm_card_interval
public import Theorems.Thm_card_rectPtSet
public import Theorems.Thm_card_rectPtsetSubsetMatrix
public import Theorems.Thm_contains_of_isEmpty
public import Theorems.Thm_ex_identityPattern_two
public import Theorems.Thm_ex_zero
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
private lemma f_pt_to_blk {n q : ℕ} (hqn : q ∣ n) {i j : Fin (n / q)} {a b : Fin n}
    (H : (a, b) ∈ rectPtsetq n q i j) :
    let fq (x : Fin n) : Fin (n / q) := ⟨x / q, Nat.div_lt_div_of_lt_of_dvd hqn x.isLt⟩
    fq a = i ∧ fq b = j := by
  extract_lets fq
  simp only [rectPtsetq, rectPtset, Finset.mem_Ico, mem_product, mem_filter, Finset.mem_univ,
    true_and] at H
  obtain ⟨⟨la, ua⟩, lb, ub⟩ := H
  simp only [fq]
  constructor
  · suffices ↑a / q = i from by exact Fin.eq_of_val_eq this
    apply Nat.div_eq_of_lt_le
    · rwa [mul_comm]
    · rwa [mul_comm]
  · suffices ↑b / q = j from by exact Fin.eq_of_val_eq this
    apply Nat.div_eq_of_lt_le
    · rwa [mul_comm]
    · rwa [mul_comm]
end
end

set_option autoImplicit true
@[expose] public section
public section
open Finset Set OrderDual Equiv
variable {k n q : ℕ}
open scoped Classical
theorem _root_.solution (M : Fin n → Fin n → Prop)
    (hqn : q ∣ n) (f1 : Fin (n / q) → Fin (n / q) → Prop) :
    let B := blkMatrix M q
    let B1 (i j : Fin (n / q)) : Prop := B i j ∧ f1 i j
    let fq (x : Fin n) : Fin (n / q) := ⟨x / q, Nat.div_lt_div_of_lt_of_dvd hqn x.isLt⟩
    let M1 (i j : Fin n) : Prop := M i j ∧ B1 (fq i) (fq j);
    let Q := Fin (n / q) × Fin (n / q)
    density M1 = ∑ ij : Q with B1 ij.1 ij.2, blk_den M ij.1 ij.2 := by
  extract_lets B B1 fq M1 Q
  have B1_eq_blockM1 : B1 = blkMatrix M1 q := by
    simp! [B1, B, blkMatrix, M1]
    ext i j
    constructor
    · rintro ⟨⟨a, b, Hab, Hab2⟩, h_f1ij⟩
      simp only [blkMatrix, Prod.exists]
      obtain ⟨fqa, fqb⟩ : fq a = i ∧ fq b = j := f_pt_to_blk hqn Hab2
      use a, b
      rw [fqa, fqb]
      refine ⟨⟨Hab, ?_, h_f1ij⟩, Hab2⟩
      use a, b
    · intro h
      simp only [blkMatrix, Prod.exists] at h
      obtain ⟨a, b, ⟨h1, _, h2⟩ , r⟩ := h
      obtain ⟨fqa, fqb⟩ : fq a = i ∧ fq b = j := f_pt_to_blk hqn r
      rw [fqa, fqb] at h2
      refine ⟨?_, h2⟩
      use a, b
  have h_only_M1 :
      ∑ ⟨i, j⟩ : Q with B1 i j, blk_den M i j = ∑ ⟨i, j⟩ : Q with B1 i j, blk_den M1 i j := by
    suffices ∀ p : Q, B1 p.1 p.2 → (blk_den M p.1 p.2 = blk_den M1 p.1 p.2) by
      let s : Finset Q := {p : Q | B1 p.1 p.2}
      change ∑ p ∈ s, blk_den M p.1 p.2 = ∑ p ∈ s, blk_den M1 p.1 p.2
      rw [Finset.sum_eq_sum_iff_of_le] <;> aesop
    intro p hp
    simp only [blk_den]
    suffices rectPtsetqMatrix M q p.1 p.2 = rectPtsetqMatrix M1 q p.1 p.2 by rw [this]
    simp only [M1]
    simp only [blkMatrix, Prod.exists, B1, B] at hp
    obtain ⟨⟨a, b, _, H⟩, _⟩ := hp
    ext x
    simp only [rectPtsetqMatrix,  Prod.mk.eta, mem_filter, Finset.mem_univ, true_and,
      and_congr_left_iff, iff_self_and]
    intro hx hx2
    simp only [blkMatrix, Prod.exists, B1, B]
    obtain ⟨lx, rx⟩ : fq x.1 = p.1 ∧ fq x.2 = p.2 := f_pt_to_blk hqn hx
    exact ⟨⟨a, b, by aesop⟩, by aesop⟩
  simp only at h_only_M1
  have := den_eq_sum_blk_den M1 hqn
  simp only at this
  simp only [B1]
  conv at this =>
    conv =>
      enter [2, 1, 1]
      intro
      rw [← B1_eq_blockM1]
    right
    rw [← h_only_M1]
  exact this
