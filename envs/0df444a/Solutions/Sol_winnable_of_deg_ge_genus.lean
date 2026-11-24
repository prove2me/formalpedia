-- Prove2me | solution 1 for winnable_of_deg_ge_genus
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:52:03.135197+00:00
-- url     : https://prove2.me/submissions/53627c81-c971-4430-8bf5-1c699ec96cfa

module
public import Definitions.Def_ChipFiringWithLean_Orientation
public import Definitions.Def_ChipFiringWithLean_Rank
public import Definitions.Def_ChipFiringWithLean_RRGHelpers
public import Theorems.Thm_config_degree_mono
public import Theorems.Thm_config_eff
public import Theorems.Thm_exists_q_reduced_representative
public import Theorems.Thm_linear_equiv_preserves_deg
public import Theorems.Thm_maximal_superstable_exists
public import Theorems.Thm_maximal_superstable_orientation
public import Theorems.Thm_q_reduced_superstable_correspondence

section
@[expose] public section
set_option trace.split.failure true
open Multiset Finset
private lemma degree_max_superstable {G : CFGraph} {q : G.V} (c : Config G q) (h_max : maximal_superstable G c): config_degree c = genus G := by
  have := maximal_superstable_orientation G q c h_max
  rcases this with ⟨O, hO, h_orient_eq⟩
  rw [← h_orient_eq]
  exact config_degree_from_O O hO
private lemma superstable_degree_le_genus (G : CFGraph) (q : G.V) (c : Config G q) :
  superstable G q c → config_degree c ≤ genus G := by
  intro h_super
  rcases maximal_superstable_exists G q c h_super with ⟨c_max, h_maximal, h_ge_c⟩
  rw [← degree_max_superstable c_max h_maximal]
  exact config_degree_mono h_ge_c
end
end

set_option autoImplicit true
@[expose] public section
public section
set_option trace.split.failure true
open Multiset Finset
theorem _root_.solution {G : CFGraph} (h_conn : graph_connected G) (D : CFDiv G) : deg D ≥ genus G → winnable G D := by
  intro h_deg_ge_g
  let q := Classical.arbitrary G.V
  rcases (exists_q_reduced_representative h_conn q D) with ⟨D_qred, h_equiv, h_qred⟩
  rcases (q_reduced_superstable_correspondence G q D_qred).mp h_qred with ⟨c, h_super, h_D_eq⟩
  have h_deg_c : config_degree c ≤ genus G := superstable_degree_le_genus G q c h_super
  have D_deg : deg D = deg D_qred := linear_equiv_preserves_deg G D D_qred h_equiv
  refine ⟨D_qred, ?_, h_equiv⟩
  -- D_qred = toDiv (deg D_qred) c is effective: there are enough chips at q, since
  -- deg D_qred ≥ g ≥ config_degree c
  rw [h_D_eq]
  exact (config_eff _ c).mpr (by linarith)
