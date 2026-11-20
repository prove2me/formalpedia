-- Prove2me | solution 1 for ex_permPattern_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:14:24.918803+00:00
-- url     : https://prove2.me/submissions/26267327-694d-46c0-991e-276aa6151544

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
public import Theorems.Thm_ex_perm_recurrence
public import Theorems.Thm_Fin_natCast_val_eq_zmodFinEquiv
public import Theorems.Thm_card_interval
public import Theorems.Thm_card_rectPtSet
public import Theorems.Thm_card_rectPtsetSubsetMatrix
public import Theorems.Thm_contains_of_isEmpty
public import Theorems.Thm_density_le_ex_of_not_contains
public import Theorems.Thm_density_mono
public import Theorems.Thm_ex_identityPattern_two
public import Theorems.Thm_ex_le_sq
public import Theorems.Thm_ex_zero
public import Theorems.Thm_exists_av_and_ex_eq
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
private lemma ex_permutation_to_dvd (σ : Perm (Fin k)) (n : ℕ) (hkn : k ^ 2 < n) :
    let n' : ℕ := n - n % k ^ 2
    ex (PermPattern σ) n ≤ ex (PermPattern σ) n' + 2 * k ^ 2 * n := by
  classical
  obtain rfl | hk₁ := eq_zero_or_neZero k
  · simp [Subsingleton.elim σ (.refl _)]
  extract_lets n'
  observe : 0 < n
  observe o1 : k ^ 2 ∣ n'
  observe o_le : n' ≤ n
  observe : 0 < k ^ 2
  have n'_pos : 0 < n' := by
    observe o1 : n % k ^ 2 < k ^ 2
    calc
      0 < k ^ 2 - n % k ^ 2 := Nat.zero_lt_sub_of_lt o1
      _ < n - n % k ^ 2 := by gcongr; exact o1.le
      _ = n' := by simp [n']
  have h_nn' : n - n' ≤ k ^ 2 := by
    have h1 : n - n'= n % k ^ 2 := by simp [n', tsub_tsub_cancel_of_le <| Nat.mod_le ..]
    have h2 : n % k ^ 2 < k ^ 2 := by apply Nat.mod_lt n; trivial
    observe h3 : n % k ^ 2 ≤ k ^ 2
    calc
      n - n' = n % k ^ 2 := h1
      _ ≤ k ^ 2 := h3
  obtain ⟨M, M_av_perm, M_max⟩ :
      ∃ M, ¬ Contains (PermPattern σ) M ∧ ex (PermPattern σ) n = density M := by
    apply exists_av_and_ex_eq; simp [PermPattern]
  let I : Finset (Fin n) := {a | ↑a ∈ Finset.Ico n' n}
  have h_out i : i ∉ I → ↑i < n' := by contrapose!; simp [I, n']
  let T (i j : Fin n) : Prop := (i, j) ∈ Finset.univ ×ˢ I
  let W (i j : Fin n) : Prop := (i, j) ∈ I ×ˢ Finset.univ
  let P (i j : Fin n) : Prop := T i j ∨ W i j
  have denP : density P ≤ 2 * n * (n - n') := by
    simp only [density, mem_product, Finset.mem_univ, true_and, and_true, P, T, W]
    let s : Finset (Fin n × Fin n) := Finset.univ ×ˢ I
    let t : Finset (Fin n × Fin n) := I ×ˢ Finset.univ
    obtain ⟨s_card, t_card⟩ : #s = n * (n - n') ∧ #t = n * (n - n') := by
      constructor <;>
      · simp only [card_product, card_univ, Fintype.card_fin, mul_comm, mul_eq_mul_left_iff, s, t]
        left
        dsimp [I]
        have : #{a : Fin n | ↑a ∈ Finset.Ico n' n} = #(.Ico n' n) := by apply card_interval; rfl
        aesop
    let P_pts := filter (fun x : Fin n × Fin n ↦ x.2 ∈ I ∨ x.1 ∈ I) Finset.univ
    have : P_pts = (s ∪ t) := by aesop
    calc
      #P_pts = #(s ∪ t) := congrArg card this
      _ ≤ #s + #t := Finset.card_union_le s t
      _ = 2 * n * (n - n') := by rw [s_card, t_card, mul_assoc, two_mul]
  let M1 (i j : Fin n) : Prop := M i j ∧  P i j
  let M2 (i j : Fin n) : Prop := M i j ∧ ¬ P i j
  have dM1 := calc
        density M1
    _ ≤ density P := density_mono fun _ _ h => h.2
    _ ≤ 2 * n * (n - n') := denP
    _ ≤ 2 * k ^ 2 * n := by
      conv =>
        right
        conv =>
          rw [mul_assoc]
          right
          rw [mul_comm]
        rw [← mul_assoc]
      exact Nat.mul_le_mul_left (2 * n) h_nn'
  have dM2 : density M2 ≤ ex (PermPattern σ) n' := by
    let M' (i j : Fin n') : Prop := M (i.castLE ‹_›) (j.castLE ‹_›)
    let fr : Fin n → Fin n' := fun i ↦ if h : i ∉ I then ⟨i, h_out i h⟩ else ⟨0, n'_pos⟩
    suffices claim : ¬ Contains (PermPattern σ) M' by
      let s : Finset (Fin n × Fin n) := {(x, y)| M2 x y}
      let t : Finset (Fin n' × Fin n') := {(x, y)| M' x y}
      have card_st : #s = #t := by
        apply Finset.card_bij (fun a  _ ↦ (fr a.1, fr a.2)) ?hi ?i_inj ?i_surj
        · intro a ha
          simp only [mem_filter, Finset.mem_univ, true_and, t, M']--, P, W, T, I]
          simp only [mem_filter, Finset.mem_univ, true_and, s] at ha
          simp only [mem_product, Finset.mem_univ, true_and, and_true, not_or, M2, P, T, W] at ha
          obtain ⟨_, A, B⟩ := ha
          simpa [fr, A, B]
        · intro a ha b hb' H
          simp only [Prod.mk.injEq] at H
          simp only [mem_product, Finset.mem_univ, true_and, and_true, not_or, mem_filter, s, M2, P,
            T, W] at ha hb'
          obtain ⟨l, r⟩ := H
          obtain ⟨_, a2, a1⟩ := ha
          obtain ⟨_, b2, b1⟩ := hb'
          simp only [dite_not, a1, ↓reduceDIte, b1, Fin.mk.injEq, a2, b2, fr] at l r
          rw [@Fin.val_eq_val] at l r
          exact Prod.ext l r
        · intro b hb
          simp only [mem_filter, Finset.mem_univ, true_and, t, M'] at hb
          simp only [mem_filter, Finset.mem_univ, true_and, exists_prop, Prod.exists, s]
          use b.1.castLE ‹_›, b.2.castLE ‹_›
          simp [M2, P, T, W, fr, hb, I]
      calc
        density M2 = #s := by simp [density, s]
        _ = #t := card_st
        _ = density M' := by simp [density, t]
        _ ≤ ex (PermPattern σ) n' := density_le_ex_of_not_contains M' claim
    by_contra
    suffices Contains (PermPattern σ) M by contradiction
    obtain ⟨f, hf, g, hg, prop⟩ := this
    refine ⟨fun i ↦ (f i).castLE ‹_›, hf, fun i ↦ (g i).castLE ‹_›, hg, ?_⟩
    simpa [PermPattern] using prop
  calc
    ex (PermPattern σ) n = density M := M_max
    _ = density M1 + density M2 := split_density M P
    _ ≤ 2 * k ^ 2 * n + ex (PermPattern σ) n' := add_le_add dM1 dM2
    _ = ex (PermPattern σ) n' + 2 * k ^ 2 * n := by rw [Nat.add_comm]
end
end

set_option autoImplicit true
@[expose] public section
public section
open Finset Set OrderDual Equiv
variable {k n q : ℕ}
theorem _root_.solution (σ : Perm (Fin k)) (n : ℕ) :
    ex (PermPattern σ) n ≤ 2 * k ^ 4 * (k ^ 2).choose k * n := by
  obtain rfl | hk₁ := eq_or_ne k 0
  · simp [Subsingleton.elim σ (.refl _)]
  obtain rfl | hk₁ := eq_or_ne k 1
  · simp [Subsingleton.elim σ (.refl _)]
  induction n using Nat.strong_induction_on with | h n ih
  observe : k ^ 2 > 0
  observe : 0 < k
  have : k ≤ k ^ 2 := by
    rw [Nat.pow_two]
    exact Nat.le_mul_of_pos_left k this
  let K := (k ^ 2).choose k
  observe : 0 < K
  obtain rfl | n_pos := eq_zero_or_pos n
  · simp
  obtain base | h_k := le_or_gt n (k ^ 2)
  · -- base case is trivial
    calc
      ex (PermPattern σ) n ≤ n^2 := ex_le_sq n
      _ ≤ k ^ 2 * n := by rw [Nat.pow_two]; exact Nat.mul_le_mul_right n base
      _ ≤ 2 * k ^ 4 * n := by
        have : k ^ 2 ≤ k ^ 4 := by gcongr; lia
        have : k ^ 2 ≤ 2 * k ^ 4 := by lia
        exact Nat.mul_le_mul_right n this
      _ ≤ 2 * k ^ 4* K * n := by aesop
  · let n' : ℕ := n - n % k ^ 2
    observe hkn : k ^ 2 < n
    observe n_non_zero : NeZero n
    observe o1 : k ^ 2 ∣ n'
    observe o_le : n' ≤ n
    have o2 : 0 < n' := by
      observe o1 : n % k ^ 2 < k ^ 2
      calc
        0 < k ^ 2 - n % k ^ 2 := Nat.zero_lt_sub_of_lt o1
        _ < n - n % k ^ 2 := by gcongr; exact o1.le
        _ = n' := by simp [n']
    observe o3 : NeZero n'
    have o4 : n' / k ^ 2 < n := by
      have : 1 < k ^ 2 := by lia
      observe : n' / k ^ 2 < n'
      calc
        n' / k ^ 2 < n' := this
        _ ≤ n := o_le
    have ez_eq1 : 2 * k ^ 4 * K * (n' / k ^ 2) = 2 * (k ^ 2 * K * n') := by
      suffices k ^ 4 * K * (n' / k ^ 2) = k ^ 2 * K * n' by simpa [mul_assoc]
      have : k ^ 4 * (n' / k ^ 2) = k ^ 2 * n' := by
        suffices k ^ 4 * (n' / k ^ 2) = (k ^ 4/k ^ 2) * n' by
          rw [this]
          rw [Nat.pow_div (by lia)]
          trivial
        have : k ^ 2 ∣ k ^ 4 := pow_dvd_pow _ <| by lia
        rw [Nat.pow_div]
        any_goals trivial
        rw [← Nat.mul_div_assoc (k ^ 4), mul_comm, Nat.mul_div_assoc n' this, Nat.pow_div]
        any_goals trivial
        simp [mul_comm]
      conv =>
        left
        conv =>
          left
          rw [mul_comm]
        rw [mul_assoc]
        rw [this]
        rw [← mul_assoc]
        left
        rw [mul_comm]
    have : (k - 1) ^ 2 + k + 1 ≤ k ^ 2 := by
      have : (k - 1) ^ 2 + k + 1 = k ^ 2 - k + 2 := by
        cases k
        · trivial
        simp [pow_two, left_distrib]
        ring
      rw [this]
      observe : k ^ 2 - k + 2 = k ^ 2 + 2 - k
      rw [this]
      lia
    calc
      ex (PermPattern σ) n
        ≤ ex (PermPattern σ) n' + 2 * k ^ 2 * n := ex_permutation_to_dvd σ n hkn
      _ ≤ (k - 1) ^ 2 * ex (PermPattern σ) (n' / k ^ 2) + 2 * n' * k ^ 3 * K + 2 * k ^ 2 * n := by
        gcongr; exact ex_perm_recurrence σ n' o1
      _ ≤ (k - 1) ^ 2 * (2 * k ^ 4 * K * (n' / k ^ 2)) + 2 * n' * k ^ 3 * K + 2 * k ^ 2 * n := by
        gcongr; exact ih (n' / k ^ 2) o4
      _ = (k - 1) ^ 2 * (2 * (k ^ 2 * K * n')) + 2 * n' * k ^ 3 * K + 2 * k ^ 2 * n := by
        rw [ez_eq1]
      _ ≤ (k - 1) ^ 2 * (2 * (k ^ 2 * K * n)) + 2 * n * k ^ 3 * K + 2 * k ^ 2 * n := by gcongr
      _ ≤ (k - 1) ^ 2 * (2 * (k ^ 2 * K * n)) + 2 * n * k ^ 3 * K + 2 * k ^ 2 * n * K := by
        aesop
      _ = (2 * k ^ 2 * n * K) * ((k - 1) ^ 2 + k + 1) := by ring
      _ ≤ (2 * k ^ 2 * n * K) * k ^ 2 := Nat.mul_le_mul_left (2 * k ^ 2 * n * K) this
      _ = 2 * k ^ 4 * K * n := by ring
