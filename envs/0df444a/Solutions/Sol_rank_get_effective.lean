-- Prove2me | solution 1 for rank_get_effective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:48:59.680969+00:00
-- url     : https://prove2.me/submissions/1b390b78-4bf4-47b3-8db7-a23b7b56f08d

module
public import Definitions.Def_ChipFiringWithLean_Basic
public import Definitions.Def_ChipFiringWithLean_Rank
public import Theorems.Thm_deg_one_chip
public import Theorems.Thm_legal_set_empty
attribute [local simp] deg_one_chip
attribute [local simp] legal_set_empty


section
@[expose] public section
set_option trace.split.failure true
open Multiset Finset
private lemma rank_spec (G : CFGraph) (D : CFDiv G) : rank_eq G D (rank G D) :=
  Classical.choose_spec (rank_exists G D)
end
end

set_option autoImplicit true
@[expose] public section
public section
set_option trace.split.failure true
open Multiset Finset
theorem _root_.solution (G : CFGraph) (D : CFDiv G) :
  ∃ E : CFDiv G, effective E ∧ deg E = rank G D + 1 ∧ ¬(winnable G (D-E)) := by
  obtain ⟨_, h_r_not_geq⟩ := rank_spec G D
  dsimp only [rank_geq] at h_r_not_geq
  push Not at h_r_not_geq
  rcases h_r_not_geq with ⟨E, ⟨h_E_eff, h_E_deg⟩, h_E_not_winnable⟩
  exact ⟨E, h_E_eff, h_E_deg, h_E_not_winnable⟩
