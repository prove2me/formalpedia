-- Prove2me | solution 1 for rank_geq_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:49:29.741819+00:00
-- url     : https://prove2.me/submissions/c056166c-6e3f-4949-938c-4310f8b68aa4

module
public import Definitions.Def_ChipFiringWithLean_Basic
public import Definitions.Def_ChipFiringWithLean_Rank
public import Theorems.Thm_winnable_of_effective
public import Theorems.Thm_winnable_add_winnable
public import Theorems.Thm_lt_of_rank_geq_not
public import Theorems.Thm_deg_one_chip
public import Theorems.Thm_legal_set_empty
attribute [local simp] deg_one_chip
attribute [local simp] legal_set_empty


section
@[expose] public section
set_option trace.split.failure true
open Multiset Finset
private lemma rank_geq_trans (G : CFGraph) (D : CFDiv G) (r1 r2 : ℤ) :
  rank_geq G D r1 → r2 ≤ r1 → rank_geq G D r2 := by
  intro h_r1 h_leq
  unfold rank_geq at *
  contrapose! h_r1
  rcases h_r1 with ⟨E, ⟨h_E_eff,h_E_nonwin⟩⟩
  rcases eff_of_degree_nonempty G (sub_nonneg.mpr h_leq) with ⟨E_diff, h_Ediff_eff, h_Ediff_deg⟩
  use E + E_diff
  constructor
  · -- Show that E + E_diff is effective of degree r2
    constructor
    apply (Eff G).add_mem
    exact h_E_eff.left
    exact h_Ediff_eff
    -- Show degree
    have E_deg := h_E_eff.right
    simp only [_root_.map_add] at E_deg h_Ediff_deg ⊢
    linarith
  . -- Show that D - (E + E_diff) is not winnable
    contrapose! h_E_nonwin
    have E_diff_winnable := winnable_of_effective G E_diff h_Ediff_eff
    have sum_winnable := winnable_add_winnable G _ _ h_E_nonwin E_diff_winnable
    simpa only [sub_eq_add_neg, neg_add_rev, add_comm, add_left_comm, add_neg_cancel_comm_assoc]
        using sum_winnable
private lemma rank_spec (G : CFGraph) (D : CFDiv G) : rank_eq G D (rank G D) :=
  Classical.choose_spec (rank_exists G D)
end
end

set_option autoImplicit true
@[expose] public section
public section
set_option trace.split.failure true
open Multiset Finset
theorem _root_.solution (G : CFGraph) (D : CFDiv G) (k : ℤ) :
  rank_geq G D k ↔ rank G D ≥ k := by
  constructor
  · -- Forward direction
    intro h_rank_geq
    have := lt_of_rank_geq_not G D k (rank G D + 1) h_rank_geq (rank_spec G D).right
    linarith
  · -- Backward direction
    intro h_rank_leq
    exact rank_geq_trans G D (rank G D) k (rank_spec G D).left h_rank_leq
