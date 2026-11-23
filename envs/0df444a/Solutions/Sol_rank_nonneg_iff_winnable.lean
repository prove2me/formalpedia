-- Prove2me | solution 1 for rank_nonneg_iff_winnable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:47:09.57965+00:00
-- url     : https://prove2.me/submissions/1c40d381-93fe-4fcc-88b9-bcff40dc3eaf

module
public import Definitions.Def_ChipFiringWithLean_Basic
public import Definitions.Def_ChipFiringWithLean_Rank
public import Theorems.Thm_deg_one_chip
public import Theorems.Thm_eff_degree_zero
public import Theorems.Thm_legal_set_empty
attribute [local simp] deg_one_chip
attribute [local simp] legal_set_empty



set_option autoImplicit true
@[expose] public section
public section
set_option trace.split.failure true
open Multiset Finset
theorem _root_.solution (G : CFGraph) (D : CFDiv G) :
  rank_geq G D 0 ↔ winnable G D := by
  constructor
  · intro h_rank
    specialize h_rank 0
    rw [sub_zero] at h_rank
    exact h_rank <| by
      simp only [eff_of_degree, effective, ge_iff_le, Set.mem_ofPred_eq, Pi.zero_apply, Std.le_refl,
          implies_true, _root_.map_zero, and_self]
  · intro h_winnable E ⟨h_eff_E, h_deg_E⟩
    have E_zero := eff_degree_zero _ h_eff_E h_deg_E
    simpa only [E_zero, sub_zero] using h_winnable
