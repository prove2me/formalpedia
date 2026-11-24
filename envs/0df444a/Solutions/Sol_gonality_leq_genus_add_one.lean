-- Prove2me | solution 1 for gonality_leq_genus_add_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:53:51.167263+00:00
-- url     : https://prove2.me/submissions/12a039d1-b7b7-4b27-8069-d8928aec35b2

module
public import Definitions.Def_ChipFiringWithLean_RRGHelpers
public import Definitions.Def_ChipFiringWithLean_RiemannRoch
public import Theorems.Thm_deg_one_chip
public import Theorems.Thm_legal_set_empty
public import Theorems.Thm_rank_geq_iff
public import Theorems.Thm_winnable_of_deg_ge_genus
attribute [local simp] deg_one_chip
attribute [local simp] legal_set_empty



set_option autoImplicit true
@[expose] public section
public section
set_option trace.split.failure true
universe u
open Multiset Finset
theorem _root_.solution
    {G : CFGraph} (h_conn : graph_connected G) : gonality_leq G (genus G + 1) := by
  let q : G.V := Classical.arbitrary G.V
  let D : CFDiv G := (genus G + 1) • one_chip q
  have h_deg_D : deg D = genus G + 1 := by
    dsimp only [D]
    rw [map_zsmul, deg_one_chip, zsmul_one]
    simp only [Int.cast_add, Int.cast_eq, Int.cast_one]
  have h_rank_geq : rank_geq G D 1 := by
    intro E hE
    dsimp only [eff_of_degree, Set.mem_ofPred_eq] at hE
    rcases hE with ⟨hE_eff, hE_deg⟩
    have h_deg_sub : deg (D - E) = genus G := by
      rw [deg.map_sub, h_deg_D, hE_deg]
      ring
    apply winnable_of_deg_ge_genus h_conn (D - E)
    rw [h_deg_sub]
  refine ⟨D, (rank_geq_iff G D 1).mp h_rank_geq, h_deg_D⟩
