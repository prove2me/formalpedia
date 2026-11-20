-- Prove2me | solution 1 for ex_perm_recurrence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:13:41.365316+00:00
-- url     : https://prove2.me/submissions/fd1d7e8f-b9a7-4bb0-8bd3-dfe2c1a2945f

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
public import Theorems.Thm_split_density_blk
public import Theorems.Thm_sum_blk_den_le_mul_den_blk
public import Theorems.Thm_av_perm_contract_av_perm
public import Theorems.Thm_density_WB
public import Theorems.Thm_density_TB
public import Theorems.Thm_blk_den_SB
public import Theorems.Thm_Fin_natCast_val_eq_zmodFinEquiv
public import Theorems.Thm_card_interval
public import Theorems.Thm_card_rectPtSet
public import Theorems.Thm_card_rectPtsetSubsetMatrix
public import Theorems.Thm_contains_of_isEmpty
public import Theorems.Thm_density_le_ex_of_not_contains
public import Theorems.Thm_ex_identityPattern_two
public import Theorems.Thm_ex_zero
public import Theorems.Thm_exists_av_and_ex_eq
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
private lemma blk_den_k4 (hkn : k ^ 2 ∣ n) (M : Fin n → Fin n → Prop) :
    let q := k ^ 2
    ∀ i j : Fin (n / q), blk_den M i j ≤ k ^ 4 := by
  extract_lets q
  observe hqn : q ∣ n
  intro i j
  have := card_rectPtsetqMatrix M hqn i j (by aesop)
  simp only [blk_den, ge_iff_le]
  simp only [q] at this
  simp only [q]
  suffices k ^ 4 = k ^ 2 * k ^ 2 by rwa [this]
  simpa using Nat.pow_add k 2 2
private lemma k_pow_n_mul (hkn : k ^ 2 ∣ n) :
    k ^ 4 * (n / k ^ 2 * (k * (k ^ 2).choose k)) = n * k ^ 3 * (k ^ 2).choose k := calc
      k ^ 4 * (n / k ^ 2 * (k * (k ^ 2).choose k))
  _ = (n / k ^ 2 * k ^ 2) * k ^ 3 * (k ^ 2).choose k := by group
  _ = n * k ^ 3 * (k ^ 2).choose k := by rw [Nat.div_mul_cancel ‹_›]
end
end

set_option autoImplicit true
@[expose] public section
public section
open Finset Set OrderDual Equiv
variable {k n q : ℕ}
theorem _root_.solution (σ : Perm (Fin k)) (n : ℕ) (hkn : k ^ 2 ∣ n) :
    ex (PermPattern σ) n
      ≤ (k - 1) ^ 2 * ex (PermPattern σ) (n / k ^ 2) + 2 * n * k ^ 3 * (k ^ 2).choose k := by
  classical
  obtain rfl | hn := eq_zero_or_neZero n
  · simp
  obtain rfl | hk := eq_zero_or_neZero k
  · simp [NeZero.ne n] at hkn
  obtain ⟨M, M_av_perm, M_max⟩ :
      ∃ M, ¬ Contains (PermPattern σ) M ∧ ex (PermPattern σ) n = density M := by
    apply exists_av_and_ex_eq; simp [PermPattern]
  let q : ℕ := k ^ 2
  let B := blkMatrix M q
  let Q := Fin (n / q) × Fin (n / q)
  let W (i j : Fin (n / q)) : Prop := k ≤ #{c | ∃ r, (r, c) ∈ rectPtsetqMatrix M q i j}
  let T (i j : Fin (n / q)) : Prop := k ≤ #{r | ∃ c, (r, c) ∈ rectPtsetqMatrix M q i j}
  let S (i j : Fin (n / q)) : Prop := ¬ W i j ∧ ¬ T i j
  let WB (i j : Fin (n / q)) : Prop := W i j ∧ B i j
  let TB (i j : Fin (n / q)) : Prop := T i j ∧ B i j
  let SB (i j : Fin (n / q)) : Prop := S i j ∧ B i j
  let K := (k ^ 2).choose k
  let sum_SB := ∑ ⟨i, j⟩ : Q with SB i j, blk_den M i j
  let sum_WB := ∑ ⟨i, j⟩ : Q with WB i j, blk_den M i j
  let sum_TB := ∑ ⟨i, j⟩ : Q with TB i j, blk_den M i j
  observe q_dvd_n : q ∣ n
  have den_le_sum : density M ≤ sum_WB + sum_TB + sum_SB := by
    simpa [WB, B, and_comm (a := blkMatrix ..), sum_SB, sum_WB, sum_TB]
      using split_density_blk q_dvd_n M W T
  have h_sum_SB : sum_SB ≤ (k - 1) ^ 2 * ex (PermPattern σ) (n / k ^ 2) := by
    change ∑ ⟨i, j⟩ : Q with SB i j, blk_den M i j ≤ (k - 1) ^ 2 * ex (PermPattern σ) (n / k ^ 2)
    have h1 : ∀ (i j : Fin (n / q)), SB i j → blk_den M i j ≤ (k - 1) ^ 2 := by
      convert blk_den_SB k M
    have h2 : density SB ≤ ex (PermPattern σ) (n / q) := by
      suffices ¬ Contains (PermPattern σ) SB from density_le_ex_of_not_contains SB this
      show ¬ Contains (PermPattern σ) SB
      · by_contra
        simp only [Contains, SB] at this
        obtain ⟨f, hf, g, hg, H⟩ := this
        refine av_perm_contract_av_perm q _ M M_av_perm ?_
        simp only [Contains]
        refine ⟨f, hf, g, hg, ?_⟩
        show ∀ (a b : Fin k), PermPattern σ a b → blkMatrix M q (f a) (g b)
        intros
        simp_all only [- M_av_perm, ge_iff_le, not_le, and_imp, q, SB, S, W, T, B]
    calc
      ∑ ⟨i, j⟩ : Q with SB i j, blk_den M i j ≤ (k - 1) ^ 2 * density SB := by
        convert sum_blk_den_le_mul_den_blk M SB h1
      _ ≤ (k - 1) ^ 2 * ex (PermPattern σ) (n / q) := Nat.mul_le_mul_left ((k - 1) ^ 2) h2
  have : sum_WB ≤ n * k ^ 3 * K := by
    change ∑ ⟨i, j⟩ : Q with WB i j, blk_den M i j ≤ n * k ^ 3 * K
    have blk_den_trivial : ∀ (i j : Fin (n / q)), blk_den M i j ≤ k ^ 4 := by
      apply blk_den_k4
      simp_all
    observe h1 : ∀ (i j : Fin (n / q)), WB i j → blk_den M i j ≤ k ^ 4
    calc
      ∑ ⟨i, j⟩ : Q with WB i j, blk_den M i j
        ≤ k ^ 4 * density WB := by convert sum_blk_den_le_mul_den_blk M WB h1
      _ ≤ k ^ 4 * ((n / k ^ 2) * (k * K)) := by
        gcongr
        exact density_WB (NeZero.pos _) hkn M M_av_perm
      _ = n * k ^ 3 * K := k_pow_n_mul hkn
  have : sum_TB ≤ n * k ^ 3 * K := by
    change ∑ ⟨i, j⟩ : Q with TB i j, blk_den M i j ≤ n * k ^ 3 * K
    have blk_den_trivial : ∀ (i j : Fin (n / q)), blk_den M i j ≤ k ^ 4 := by
      apply blk_den_k4
      simp_all
    observe h1 : ∀ (i j : Fin (n / q)), TB i j → blk_den M i j ≤ k ^ 4
    calc
      ∑ ⟨i, j⟩ : Q with TB i j, blk_den M i j
        ≤ k ^ 4 * density TB := by convert sum_blk_den_le_mul_den_blk M TB h1
      _ ≤ k ^ 4 * ((n / k ^ 2) * (k * K)) := by
        gcongr; exact density_TB (NeZero.pos _) hkn M M_av_perm
      _ = n * k ^ 3 * K := k_pow_n_mul hkn
  have h_sum_WB_TB : sum_WB + sum_TB ≤ 2 * (n * k ^ 3 * K) := by lia
  calc
    ex (PermPattern σ) n
    _ = density M := M_max
    _ ≤ sum_WB + sum_TB + sum_SB := den_le_sum
    _ ≤ 2 * (n * k ^ 3 * K) + sum_SB := Nat.add_le_add_right h_sum_WB_TB sum_SB
    _ ≤ 2 * (n * k ^ 3 * K) + (k - 1) ^ 2 * ex (PermPattern σ) (n/k ^ 2) := by gcongr
    _ = (k - 1) ^ 2 * ex (PermPattern σ) (n / k ^ 2) + 2 * n * k ^ 3 * K := by ring
