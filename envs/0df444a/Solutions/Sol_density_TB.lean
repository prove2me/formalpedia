-- Prove2me | solution 1 for density_TB
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:11:16.655651+00:00
-- url     : https://prove2.me/submissions/dc41181d-89e1-4758-ab28-4bbeebf19bfd

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
public import Theorems.Thm_Fin_natCast_val_eq_zmodFinEquiv
public import Theorems.Thm_card_interval
public import Theorems.Thm_card_rectPtSet
public import Theorems.Thm_card_rectPtsetSubsetMatrix
public import Theorems.Thm_contains_of_isEmpty
public import Theorems.Thm_density_by_rows_ub
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
end
end

set_option autoImplicit true
@[expose] public section
public section
open Finset Set OrderDual Equiv
variable {k n q : ℕ}
theorem _root_.solution {n k : ℕ} (h_n : 0 < n) (h_k : k ^ 2 ∣ n) (M : Fin n → Fin n → Prop)
    {σ : Perm (Fin k)} (M_avoid_perm : ¬ Contains (PermPattern σ) M) :
    let q := k ^ 2
    let B := blkMatrix M q
    let T (i j : Fin (n / q)) : Prop := k ≤ #{r | ∃ c, (r, c) ∈ rectPtsetqMatrix M q i j}
    let TB : Fin (n / q) → Fin (n / q) → Prop := fun i j ↦ T i j ∧ B i j
    density TB ≤ n / k ^ 2 * (k * (k ^ 2).choose k) := by
  classical
  let q := k ^ 2
  let B := blkMatrix M q
  let T (i j : Fin (n / q)) : Prop := k ≤ #{r | ∃ c, (r, c) ∈ rectPtsetqMatrix M q i j}
  let TB : Fin (n / q) → Fin (n / q) → Prop := fun i j ↦ T i j ∧ B i j
  suffices ∀ i, row_density TB i ≤ k * q.choose k from density_by_rows_ub TB this
  intro i
  by_contra! h_contra
  let R : Finset (Fin n) := {a : Fin n | ↑a ∈ Finset.Ico (q * i) (q * (i+1))}
  have TB_k_row j (_ : TB i j) :
      ∃ s ⊆ ({r | ∃ c, (r, c) ∈ rectPtsetqMatrix M q i j} : Finset (Fin n)), #s = k := by
    apply Finset.exists_subset_card_eq
    simp_all [TB, T]
  let f : Fin (n / q) → Finset (Fin n) := fun j ↦ if h : TB i j then (TB_k_row j h).choose else ∅
  let s := ({j | TB i j} : Finset (Fin (n / q))) -- all tall blocks
  let t := Finset.powersetCard k R -- all subset of the rows of size k
  obtain ⟨S, hs, hs'⟩ : ∃ C' ∈ t, k - 1 < #{i ∈ s | f i = C'} := by
    apply exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    · --  ∀ a ∈ s, f a ∈ t
      simp only [mem_filter, Finset.mem_univ, true_and, mem_powersetCard, and_imp, s, TB, t]
      intro j ha1 ha2
      observe h : TB i j
      observe : T i j ∧ B i j
      constructor
      · -- ⊢
        intro x hx
        simp only [Finset.mem_Ico, mem_filter, Finset.mem_univ, true_and, R]
        simp only [f, this, and_self, ↓reduceDIte, TB] at hx
        have := (TB_k_row j h).choose_spec.1
        simp only [rectPtsetqMatrix, rectPtsetq, rectPtset, Finset.mem_Ico, Prod.mk.eta,
          mem_product, mem_filter, Finset.mem_univ, true_and] at this
        rw [Finset.subset_iff] at this
        have :
            x ∈ ({r | ∃ c, M r c ∧
              (q * ↑i ≤ ↑r ∧ ↑r < q * (↑i + 1)) ∧ q * ↑j ≤ ↑c ∧ ↑c < q * (↑j + 1)} : Finset _) := by
          apply this
          convert hx
          simp only [rectPtsetqMatrix, rectPtsetq, rectPtset, Finset.mem_Ico, Prod.mk.eta,
            mem_product, mem_filter, Finset.mem_univ, true_and]
        simp only [mem_filter, Finset.mem_univ, true_and] at this
        obtain ⟨_, _, l, _, _⟩ := this
        exact l
      · -- ⊢
        simpa [f, TB, h] using (TB_k_row j h).choose_spec.2
    · -- ⊢ #t * (k - 1) < #s
      have tcard_eq_qck : #t = (q.choose k) := by
        simp only [card_powersetCard, t, q]
        suffices #R = k ^ 2 by rw [this]
        dsimp [R]
        refine card_intervalq n q ↑i h_n h_k ?h
        · -- ⊢ ↑j < n / q
          simp only [Fin.is_lt]
      calc
        #t * (k - 1)
        _ = (k - 1) * q.choose k := by rw [tcard_eq_qck, mul_comm]
        _ ≤ k * q.choose k := by gcongr; lia
        _ < #s := by simpa [row_density, TB, s] using h_contra
  simp only [mem_powersetCard, t] at hs
  obtain ⟨s_subset_R, s_card_k⟩ := hs
  suffices Contains (PermPattern σ) M by contradiction
  let RB := (filter (fun i ↦ f i = S) s)
  replace hs' : k ≤ #RB := by exact Nat.le_of_pred_lt hs'
  let f' := S.orderEmbOfFin s_card_k
  observe f_mono : StrictMono f'
  let g' := RB.orderEmbOfCardLe hs'
  have g'_prop j : ∃ p, M p.1 p.2 ∧ p ∈ rectPtsetq n q i (g' j) ∧ p.1 = f' (σ⁻¹ j) := by
    have := RB.orderEmbOfCardLe_mem hs' j
    simp only [mem_filter, RB] at this
    obtain ⟨h1, h2⟩ := this
    replace h2 : f (g' j) = S := by congr
    replace h1 : g' j ∈ s := by congr
    simp only [f, TB] at h2
    simp only [mem_filter, Finset.mem_univ, true_and, s, TB] at h1
    obtain ⟨h4, h3⟩ := h1
    simp only [h4, h3, and_self, ↓reduceDIte] at h2
    observe h : TB i (g' j)
    have := (TB_k_row (g' j) h).choose_spec.1
    rw [h2] at this
    observe f'_pi : f' (σ⁻¹ j) ∈ S
    simp only [subset_iff, mem_filter, Finset.mem_univ, true_and] at this
    obtain ⟨c, hc⟩ : ∃ c, (f' (σ⁻¹ j), c) ∈ rectPtsetqMatrix M q ↑i  ↑(g' j) := this f'_pi
    simp only [rectPtsetqMatrix, Prod.mk.eta, mem_filter, Finset.mem_univ, true_and] at hc
    obtain ⟨hr1, hr2⟩ := hc
    use (f' (σ⁻¹ j), c)
  let g := fun i : Fin k ↦ (g'_prop i).choose.2
  refine ⟨f', f_mono, g, ?_, ?_⟩
  · intro a b hab
    replace ha := (g'_prop a).choose_spec.2.1;
    simp only [rectPtsetq, rectPtset, Finset.mem_Ico, mem_product, mem_filter, Finset.mem_univ,
      true_and, Perm.coe_inv] at ha
    replace hb := (g'_prop b).choose_spec.2.1
    simp only [rectPtsetq, rectPtset, Finset.mem_Ico, mem_product, mem_filter, Finset.mem_univ,
      true_and, Perm.coe_inv] at hb
    obtain ⟨_, _, ha_ub⟩ := ha
    obtain ⟨_, hb_lb, _⟩ := hb
    observe : g' a < g' b
    observe : (g' a : ℕ) + 1 ≤ (g' b : ℕ)
    calc
      g a < q * (g' a + 1) := by simpa [rectPtsetq, rectPtset, g] using ha_ub
      _ ≤ q * g' b := by gcongr
      _ ≤ g b := by simpa [rectPtsetq, rectPtset, g] using hb_lb
  · -- show embedding of permutation
    simp only [PermPattern, forall_eq']
    have : (∀ a, M (f' (σ⁻¹ a)) (g a)) ↔ ∀ a, M (f' a) (g (σ a)) := σ⁻¹.forall_congr (by simp)
    rewrite [← this]
    intro j
    obtain ⟨H, _, H'⟩ := (g'_prop j).choose_spec
    simp only [g]
    rwa [H'] at H
