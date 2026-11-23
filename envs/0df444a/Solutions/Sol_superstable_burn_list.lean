-- Prove2me | solution 1 for superstable_burn_list
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:48:37.142166+00:00
-- url     : https://prove2.me/submissions/9450f96f-4e4d-4c51-b4c3-1a21482cda36

module
public import Definitions.Def_ChipFiringWithLean_Basic
public import Definitions.Def_ChipFiringWithLean_Config
public import Theorems.Thm_deg_one_chip
public import Theorems.Thm_legal_set_empty
attribute [local simp] deg_one_chip
attribute [local simp] legal_set_empty


section
@[expose] public section
set_option trace.split.failure true
open Multiset Finset
private lemma burn_list_contains_q (G : CFGraph) {q : G.V} (c : Config G q) (L : List G.V) (h_bl : is_burn_list G c L) :
  L.contains q := by
  induction L with
  | nil =>
    dsimp only [is_burn_list] at h_bl
  | cons v rest ih =>
    cases rest with
    | nil =>
      dsimp only [is_burn_list] at h_bl
      rw [h_bl]
      simp only [List.contains_eq_mem, List.mem_cons, List.not_mem_nil, or_false, decide_true]
    | cons w rest' =>
      dsimp only [is_burn_list] at h_bl
      rcases h_bl with ⟨h_outdeg, h_not_in_rest, h_rest_burn_list⟩
      specialize ih h_rest_burn_list
      simp only [List.contains_eq_mem, List.mem_cons, Bool.decide_or, Bool.or_eq_true,
          decide_eq_true_eq]
      simp only [List.contains_eq_mem, List.mem_cons, Bool.decide_or, Bool.or_eq_true,
          decide_eq_true_eq] at ih
      simp only [ih, or_true]
private lemma extend_burn_list (G : CFGraph) {q : G.V} (c : Config G q) (h_ss : superstable G q c) (L : List G.V) : is_burn_list G c L → (∃ v : G.V, ¬ L.contains v) → (∃ w : G.V, w ∉ L.toFinset ∧ is_burn_list G c (w :: L)) := by
  intro h_bl h_exists_v
  let S := univ \ L.toFinset
  have h_S_ne : S.Nonempty := by
    rcases h_exists_v with ⟨v, h_v_not_in_L⟩
    use v
    dsimp only [S]
    simp only [mem_sdiff, mem_univ, List.mem_toFinset, true_and]
    contrapose! h_v_not_in_L with h_raa
    simp only [List.contains_eq_mem, h_raa, decide_true]
  have h_S_Vtilde : S ⊆ Vtilde q := by
    intro v h_v_in_S
    dsimp only [Vtilde, ne_eq]
    simp only [Finset.mem_filter, mem_univ, true_and]
    contrapose! h_v_in_S with h_eq
    rw [h_eq]
    dsimp only [S]
    simp only [mem_sdiff, mem_univ, List.mem_toFinset, true_and, Decidable.not_not]
    -- Goal is not: q ∈ L
    have := burn_list_contains_q G c L h_bl
    simp only [List.contains_eq_mem, decide_eq_true_eq] at this
    exact this
  specialize h_ss S h_S_Vtilde h_S_ne
  rcases h_ss with ⟨v, hv_in_S, hv_outdeg⟩
  use v
  dsimp only [S] at hv_outdeg hv_in_S -- To get L to simplify after matching
  match L with
  | [] =>
    exfalso
    dsimp only [is_burn_list] at h_bl
  | h :: t =>
    dsimp only [is_burn_list]
    -- Unpack all the conjunctions and use hypotheses one by one
    constructor
    . simp only [List.toFinset_cons, mem_sdiff, mem_univ, mem_insert, List.mem_toFinset, not_or,
        true_and] at hv_in_S
      simp only [List.toFinset_cons, mem_insert, List.mem_toFinset, not_or]
      exact hv_in_S
    constructor
    . exact hv_outdeg
    constructor
    simp only [List.contains_eq_mem, List.mem_cons, Bool.decide_or, Bool.or_eq_true,
        decide_eq_true_eq, not_or]
    constructor
    intro h
    rw [h] at hv_in_S
    simp only [List.toFinset_cons, mem_sdiff, mem_univ, mem_insert, List.mem_toFinset, true_or,
        not_true_eq_false, and_false] at hv_in_S
    simp only [List.toFinset_cons, mem_sdiff, mem_univ, mem_insert, List.mem_toFinset, not_or,
        true_and] at hv_in_S
    exact hv_in_S.2
    exact h_bl
private lemma burn_list_helper (G : CFGraph) {q : G.V} (c : Config G q) (h_ss : superstable G q c) (n : ℕ) : (n < Finset.card (univ : Finset G.V))→ ∃ (L : List G.V), L.toFinset.card = n+1 ∧ is_burn_list G c L := by
  intro h_n_lt_card_V
  induction n with
  | zero =>
    use [q]
    constructor
    simp only [List.toFinset_cons, List.toFinset_nil, insert_empty_eq, Finset.card_singleton,
        zero_add]
    dsimp only [is_burn_list]
  | succ n ih =>
    have ih_L : n < (univ : Finset G.V).card := by
      linarith
    apply ih at ih_L
    rcases ih_L with ⟨L, h_L_length, h_L_burn_list⟩
    have h_exists_v : ∃ v : G.V, ¬ L.contains v := by
      have h_card_L_le : L.toFinset.card < (univ : Finset G.V).card := by
        rw [← h_L_length] at h_n_lt_card_V
        linarith
      obtain ⟨v, -, h_v_not_in_L⟩ := Finset.exists_mem_notMem_of_card_lt_card h_card_L_le
      exact ⟨v, by simpa only [List.contains_eq_mem, decide_eq_true_eq, List.mem_toFinset]
          using h_v_not_in_L⟩
    have := extend_burn_list G c h_ss L h_L_burn_list h_exists_v
    rcases this with ⟨w, h_w_burn_list⟩
    use w :: L
    constructor
    . -- Show cardinality is n+2
      rw [List.toFinset_cons]
      rw [card_insert_eq_ite]
      -- Need: w ∉ L.toFinset
      simp only [h_w_burn_list.1, ↓reduceIte, Nat.add_right_cancel_iff]
      rw [h_L_length]
    . -- Show the tail is a burn list
      exact h_w_burn_list.2
end
end

set_option autoImplicit true
@[expose] public section
public section
set_option trace.split.failure true
open Multiset Finset
theorem _root_.solution (G : CFGraph) {q : G.V} (c : Config G q) (h_ss : superstable G q c) : ∃ L : burn_list G c, ∀ v : G.V, v ∈ L.list := by
  have h_card_V : (univ : Finset G.V).card ≥ 1 := by
    have h_nonempty : Nonempty G.V := by infer_instance
    have h_card_pos : (univ : Finset G.V).card > 0 := Fintype.card_pos_iff.mpr h_nonempty
    linarith
  have : (univ : Finset G.V).card - 1 < (univ : Finset G.V).card := by
    simp only [card_univ, tsub_lt_self_iff, Order.lt_one_iff, and_true]
    -- Now show `Fintype.card G.V > 0`, so that the subtraction makes sense.
    apply Fintype.card_pos_iff.mpr
    infer_instance
  have h_burn_list := burn_list_helper G c h_ss ((univ : Finset G.V).card - 1) this
  rcases h_burn_list with ⟨L, h_L_length, h_L_burn_list⟩
  have h_L_card : L.toFinset.card = (univ : Finset G.V).card := by
    simp only [h_L_length, card_univ]
    apply Nat.sub_add_cancel
    exact h_card_V
  use burn_list.mk L h_L_burn_list
  have h_toFinset_eq : L.toFinset = (univ : Finset G.V) := by
    refine Finset.eq_of_subset_of_card_le (Finset.subset_univ _) ?_
    simp only [card_univ, h_L_card, Std.le_refl]
  intro v
  have : v ∈ L.toFinset := by simp only [h_toFinset_eq, mem_univ]
  simpa only [List.mem_toFinset] using this
