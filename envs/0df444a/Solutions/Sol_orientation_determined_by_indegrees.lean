-- Prove2me | solution 1 for orientation_determined_by_indegrees
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:50:22.055967+00:00
-- url     : https://prove2.me/submissions/18eb663e-cf75-4438-ab72-36c5e5c8e72b

module
public import Definitions.Def_ChipFiringWithLean_Config
public import Mathlib.Data.DFinsupp.Multiset
public import Definitions.Def_ChipFiringWithLean_Orientation
public import Theorems.Thm_deg_one_chip
public import Theorems.Thm_legal_set_empty
attribute [local simp] deg_one_chip
attribute [local simp] legal_set_empty


section
@[expose] public section
set_option trace.split.failure true
open Multiset Finset
private lemma eq_orient {G : CFGraph} (O1 O2 : CFOrientation G) : O1 = O2 ↔ ∀ (u v : G.V), flow O1 u v = flow O2 u v := by
  constructor
  · intro h_eq u v
    rw [h_eq]
  -- Converse
  · intro h_flow_eq
    have h_directed_edges_eq : O1.directed_edges = O2.directed_edges := by
      apply Multiset.ext.mpr
      intro ⟨u,v⟩
      specialize h_flow_eq u v
      exact h_flow_eq
    cases O1
    cases O2
    cases h_directed_edges_eq
    rfl
end
end

set_option autoImplicit true
@[expose] public section
public section
set_option trace.split.failure true
open Multiset Finset
theorem _root_.solution {G : CFGraph}
  (O O' : CFOrientation G) :
  is_acyclic G O → is_acyclic G O' →
  (∀ v : G.V, indeg G O v = indeg G O' v) →
  O = O' := by
  intro h_acyc h_acyc' h_indeg_eq

  let S := { e : G.V × G.V | O.directed_edges.count e > O'.directed_edges.count e }
  have suff_S_empty : S = ∅ → O = O' := by
    intro h_S_empty
    have h_ineq (u v : G.V) : flow O u v ≤ flow O' u v := by
      have h_nin: ⟨u,v⟩ ∉ S := by
        rw [h_S_empty]
        simp only [Set.mem_empty_iff_false, not_false_eq_true]
      dsimp only [Set.mem_ofPred_eq, S] at h_nin
      linarith
    simp only [eq_orient O O']
    intro u v
    by_contra h_neq
    have h_uv_le := h_ineq u v
    have h_lt : flow O u v < flow O' u v := lt_of_le_of_ne h_uv_le h_neq
    have h_indeg_contra : indeg G O v < indeg G O' v := by
      rw [indeg_eq_sum_flow O v, indeg_eq_sum_flow O' v]
      apply Finset.sum_lt_sum
      intro x hx
      exact h_ineq x v
      use u
      simp only [mem_univ, h_lt, and_self]
    linarith [h_indeg_eq v]
  apply suff_S_empty

  -- A small helper we'll need a couple time later
  have directed_edge_of_S (e : G.V × G.V) : e ∈ S → directed_edge G O e.1 e.2 :=  by
    dsimp only [directed_edge]
    intro h
    dsimp only [Set.mem_ofPred_eq, S] at h
    have h_pos_count : count e O.directed_edges > 0 := by
      omega
    apply Multiset.count_pos.mp
    exact h_pos_count

  -- We now must show that S is empty.
  -- Do so by showing any element in S belongs to an infinite directed path
  have going_up : ∀ e ∈ S, ∃ f ∈ S, f.2 = e.1 := by
    intro e h_e_in_S
    obtain ⟨u,v⟩ := e
    by_contra! h_no_parent
    have all_flow_le : ∀ (w : G.V) , flow O w u ≤ flow O' w u := by
      intro w
      by_contra h_flow_gt
      apply lt_of_not_ge at h_flow_gt
      specialize h_no_parent ⟨w,u⟩
      simp only [ne_eq, not_true_eq_false, imp_false] at h_no_parent
      exact h_no_parent h_flow_gt
    have one_flow_lt : ∃ (w : G.V), flow O w u < flow O' w u := by
      contrapose! h_e_in_S
      dsimp only [Set.mem_ofPred_eq, S]
      suffices flow O u v ≤ flow O' u v by linarith
      specialize h_e_in_S v
      by_contra flow_lt
      apply lt_of_not_ge at flow_lt
      have edges_lt := add_lt_add_of_le_of_lt h_e_in_S flow_lt
      rw [opp_flow O v u, opp_flow O' v u] at edges_lt
      linarith

    have h: ∑ (w : G.V), flow O w u < ∑ (w : G.V), flow O' w u := by
      apply Finset.sum_lt_sum
      intro i _
      exact all_flow_le i
      rcases one_flow_lt with ⟨w, h_flow_lt⟩
      use w
      constructor
      simp only [mem_univ]
      exact h_flow_lt

    repeat rw [← indeg_eq_sum_flow] at h
    specialize h_indeg_eq u
    linarith

  -- Suppose S is nonempty, and consider the set T of vertices where an edge of S
  -- originates. By going_up, every vertex of T receives positive flow from another
  -- vertex of T, contradicting the relative source provided by subset_source.
  by_contra! h_S_nonempty
  rcases h_S_nonempty with ⟨e_start, h_e_start_in_S⟩
  classical
  let T : Finset G.V := Finset.univ.filter (fun v => ∃ e ∈ S, e.1 = v)
  have h_mem_T : ∀ v : G.V, v ∈ T ↔ ∃ e ∈ S, e.1 = v := by
    intro v
    simp only [Prod.exists, exists_and_right, exists_eq_right, Finset.mem_filter, mem_univ,
        true_and, T]
  have h_T_nonempty : T.Nonempty :=
    ⟨e_start.1, (h_mem_T e_start.1).mpr ⟨e_start, h_e_start_in_S, rfl⟩⟩
  obtain ⟨v, h_v_T, h_v_source⟩ := subset_source G O T h_T_nonempty h_acyc
  obtain ⟨e, h_e_S, h_e_fst⟩ := (h_mem_T v).mp h_v_T
  obtain ⟨f, h_f_S, h_f_snd⟩ := going_up e h_e_S
  have h_flow_pos : 0 < flow O f.1 v := by
    rw [← h_e_fst, ← h_f_snd]
    exact Multiset.count_pos.mpr (directed_edge_of_S f h_f_S)
  have h_flow_zero : flow O f.1 v = 0 :=
    h_v_source f.1 ((h_mem_T f.1).mpr ⟨f, h_f_S, rfl⟩)
  omega
