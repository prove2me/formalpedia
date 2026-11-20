-- Prove2me | solution 1 for density_WB
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:11:16.081122+00:00
-- url     : https://prove2.me/submissions/7185ea25-c57a-41ad-ab74-a49adba9ae32

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
public import Theorems.Thm_density_by_cols_ub
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
    let W (i j : Fin (n / q)) : Prop := k ≤ #{c | ∃ r, (r, c) ∈ rectPtsetqMatrix M q i j}
    let WB : Fin (n / q) → Fin (n / q) → Prop := fun i j ↦ W i j ∧ B i j
    density WB ≤ n / k ^ 2 * (k * (k ^ 2).choose k) := by
  classical
  extract_lets q B W WB
  suffices ∀ i, col_density WB i ≤ k * q.choose k from density_by_cols_ub WB this
  intro j
  by_contra! h_contra
  let C : Finset (Fin n) := {a : Fin n | ↑a ∈ Finset.Ico (q * j) (q * (j+1))}
  have WB_k_col i (hi : WB i j) :
      ∃ s ⊆ ({c | ∃ r, (r, c) ∈ rectPtsetqMatrix M q i j} : Finset (Fin n)), #s = k := by
    apply Finset.exists_subset_card_eq
    simp_all [WB, W]
  let f : Fin (n / q) → Finset (Fin n) := fun i ↦ if h : WB i j then (WB_k_col i h).choose else ∅
  let s := ({i | WB i j} : Finset (Fin (n / q))) -- all wide blocks
  let t := Finset.powersetCard k C -- all subset of the column of size k
  obtain ⟨S, hs, hs'⟩ : ∃ C' ∈ t, k - 1 < #{i ∈ s | f i = C'} := by
    apply exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    · --  ∀ a ∈ s, f a ∈ t
      simp only [mem_filter, Finset.mem_univ, true_and, mem_powersetCard, and_imp, s, WB, t]
      intro i ha1 ha2
      observe h : WB i j
      observe : W i j ∧ B i j
      simp only [f]
      constructor
      · -- ⊢ (if h : WB i j then ⋯.choose else ∅) ⊆ C
        intro x hx
        simp only [Finset.mem_Ico, mem_filter, Finset.mem_univ, true_and, C]
        simp only [this, and_self, ↓reduceDIte, WB] at hx
        have := (WB_k_col i h).choose_spec.1
        simp only [rectPtsetqMatrix, rectPtsetq, rectPtset, Finset.mem_Ico, Prod.mk.eta,
          mem_product, mem_filter, Finset.mem_univ, true_and] at this
        rw [Finset.subset_iff] at this
        have :
          x ∈ ({c | ∃ r, M r c ∧
            (q * ↑i ≤ ↑r ∧ ↑r < q * (↑i + 1)) ∧ q * ↑j ≤ ↑c ∧ ↑c < q * (↑j + 1)} : Finset _) := by
          apply this
          convert hx
          simp only [rectPtsetqMatrix, rectPtsetq, rectPtset, Finset.mem_Ico, Prod.mk.eta,
            mem_product, mem_filter, Finset.mem_univ, true_and]
        simp only [mem_filter, Finset.mem_univ, true_and] at this
        obtain ⟨_, _, _, l, r⟩ := this
        exact ⟨l, r⟩
      · -- ⊢ #(if h : WB i j then ⋯.choose else ∅) =
        simp only [h, and_self, ↓reduceDIte, WB]
        exact (WB_k_col i h).choose_spec.2
    · -- ⊢ #t * (k - 1) < #s
      have tcard_eq_qck : #t = (q.choose k) := by
        simp only [card_powersetCard, t, q]
        suffices #C = k ^ 2 by rw [this]
        dsimp [C]
        refine card_intervalq n q ↑j h_n h_k ?h
        · -- ⊢ ↑j < n / q
          simp only [Fin.is_lt]
      calc
        #t * (k - 1)
        _ = (k - 1) * q.choose k := by rw [mul_comm, tcard_eq_qck]
        _ ≤ k * q.choose k := by gcongr; lia
        _ < #s := by simpa [col_density, WB, s] using h_contra
  simp only [mem_powersetCard, t] at hs
  obtain ⟨s_subset_C, s_card_k⟩ := hs
  -- simp [f] at hp'
  suffices Contains (PermPattern σ) M by contradiction
  let RB := (filter (fun i ↦ f i = S) s)
  replace hs' : k ≤ #RB := by exact Nat.le_of_pred_lt hs'
  let g := S.orderEmbOfFin s_card_k
  observe g_mono : StrictMono g
  let f' := RB.orderEmbOfCardLe hs'
  have f'_prop i : ∃ p, M p.1 p.2 ∧ p ∈ rectPtsetq n q (f' i) j ∧ p.2 = g (σ i) := by
    have := RB.orderEmbOfCardLe_mem hs' i
    simp only [mem_filter, RB] at this
    obtain ⟨h1, h2⟩ := this
    replace h2 : f (f' i) = S := by congr
    replace h1 : f' i ∈ s := by congr
    simp only [f, WB] at h2
    simp only [mem_filter, Finset.mem_univ, true_and, s, WB] at h1
    obtain ⟨h4, h3⟩ := h1
    simp only [h4, h3, and_self, ↓reduceDIte] at h2
    observe h : WB (f' i) j
    have := (WB_k_col (f' i) h).choose_spec.1
    rw [h2] at this
    observe g_pi : g (σ i) ∈ S
    simp only [subset_iff, mem_filter, Finset.mem_univ, true_and] at this
    obtain ⟨r, hr⟩ : ∃ r, (r, (g (σ i))) ∈ rectPtsetqMatrix M q ↑(f' i) ↑j := this g_pi
    simp only [rectPtsetqMatrix, Prod.mk.eta, mem_filter, Finset.mem_univ, true_and] at hr
    obtain ⟨hr1, hr2⟩ := hr
    use (r, g (σ i))
  let f := fun i : Fin k ↦ (f'_prop i).choose.1
  have f_mono : StrictMono f := by
    simp only [StrictMono]
    intro a b hab
    have ha := (f'_prop a).choose_spec.2.1
    simp only [rectPtsetq, rectPtset, Finset.mem_Ico, mem_product, mem_filter, Finset.mem_univ,
      true_and] at ha
    have hb := (f'_prop b).choose_spec.2.1
    simp only [rectPtsetq, rectPtset, Finset.mem_Ico, mem_product, mem_filter, Finset.mem_univ,
      true_and] at hb
    obtain ⟨⟨X, ha_ub⟩, Y⟩ := ha
    obtain ⟨⟨hb_lb, XX⟩, YY⟩ := hb
    observe : f' a < f' b
    observe : ↑ (f' a : ℕ) +1 ≤ ↑(f' b : ℕ)
    calc
      f a < q * (↑(f' a) + 1) := by convert! ha_ub; simp [rectPtsetq, rectPtset]
      _ ≤ q * ↑(f' b) := by gcongr
      _ ≤ f b := by convert! hb_lb; simp [rectPtsetq, rectPtset]
  refine ⟨f, f_mono, g, g_mono, ?_⟩
  · -- show embedding of permutation
    simp only [PermPattern, forall_eq', *]
    intro i
    obtain ⟨H, _, H'⟩ := (f'_prop i).choose_spec
    simp only [f]
    rwa [H'] at H
