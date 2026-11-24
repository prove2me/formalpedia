-- Prove2me | solution 1 for gonality_geq_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:55:03.062279+00:00
-- url     : https://prove2.me/submissions/493a14a5-feea-40bb-8901-c303bf8048d3

module
public import Definitions.Def_ChipFiringWithLean_RRGHelpers
public import Definitions.Def_ChipFiringWithLean_RiemannRoch
public import Theorems.Thm_gonality_leq_genus_add_one
public import Theorems.Thm_deg_one_chip
public import Theorems.Thm_legal_set_empty
public import Theorems.Thm_rank_geq_iff
attribute [local simp] deg_one_chip
attribute [local simp] legal_set_empty


section
@[expose] public section
set_option trace.split.failure true
universe u
open Multiset Finset
private theorem one_le_of_gonality_leq {G : CFGraph} {k : ℤ} (h_gon : gonality_leq G k) : 1 ≤ k := by
  rcases h_gon with ⟨D, h_rank, h_deg⟩
  have h_rank_geq : rank_geq G D 1 := (rank_geq_iff G D 1).mpr h_rank
  have h_deg_lower : (1 : ℤ) ≤ deg D := rank_le_degree G D 1 (by norm_num) h_rank_geq
  simpa only [ge_iff_le, h_deg] using h_deg_lower
end
end

set_option autoImplicit true
@[expose] public section
public section
set_option trace.split.failure true
universe u
open Multiset Finset
theorem _root_.solution {G : CFGraph} (h_conn : graph_connected G) (k : ℤ) :
    gonality_geq G k ↔ gonality h_conn ≥ k := by
  let S : Set ℤ := {l : ℤ | gonality_leq G l}
  have h_nonempty : S.Nonempty := by
    refine ⟨genus G + 1, ?_⟩
    exact gonality_leq_genus_add_one h_conn
  have h_bdd : BddBelow S := by
    refine ⟨1, ?_⟩
    intro l hl
    exact one_le_of_gonality_leq hl
  constructor
  · intro h_geq
    dsimp only [gonality]
    refine le_csInf h_nonempty ?_
    intro l hl
    by_contra hlt
    have hlt' : l < k := by linarith
    exact h_geq l hlt' hl
  · intro h_gon l hl h_leq
    have h_inf_le : gonality h_conn ≤ l := by
      dsimp only [gonality]
      exact csInf_le h_bdd h_leq
    linarith
