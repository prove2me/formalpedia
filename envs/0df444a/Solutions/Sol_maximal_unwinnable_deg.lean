-- Prove2me | solution 1 for maximal_unwinnable_deg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:54:56.50237+00:00
-- url     : https://prove2.me/submissions/15229ace-938e-4004-9a9d-bb0defec9c94

module
public import Definitions.Def_ChipFiringWithLean_Orientation
public import Definitions.Def_ChipFiringWithLean_Rank
public import Definitions.Def_ChipFiringWithLean_RRGHelpers
public import Theorems.Thm_maximal_unwinnable_char
public import Theorems.Thm_linear_equiv_preserves_deg
public import Theorems.Thm_maximal_superstable_orientation

section
@[expose] public section
set_option trace.split.failure true
open Multiset Finset
private lemma degree_max_superstable {G : CFGraph} {q : G.V} (c : Config G q) (h_max : maximal_superstable G c): config_degree c = genus G := by
  have := maximal_superstable_orientation G q c h_max
  rcases this with ⟨O, hO, h_orient_eq⟩
  rw [← h_orient_eq]
  exact config_degree_from_O O hO
end
end

set_option autoImplicit true
@[expose] public section
public section
set_option trace.split.failure true
open Multiset Finset
theorem _root_.solution
  {G : CFGraph} (h_conn : graph_connected G) (D : CFDiv G) :
  maximal_unwinnable G D → deg D = genus G - 1 := by
  intro h_max_unwin

  let q := Classical.arbitrary G.V

  have h_char := maximal_unwinnable_char h_conn q D
  have h_max_cfg : maximal_superstable G (qReducedConfig h_conn q D) := (h_char.mp h_max_unwin).1
  have h_rep_form :
      qReducedRep h_conn q D =
        (qReducedConfig h_conn q D).chips - one_chip q := (h_char.mp h_max_unwin).2
  have h_deg_D' : deg (qReducedRep h_conn q D) = genus G - 1 := calc
    deg (qReducedRep h_conn q D) =
        deg ((qReducedConfig h_conn q D).chips - one_chip q) := by rw [h_rep_form]
    _ = config_degree (qReducedConfig h_conn q D) - 1 :=
        deg_chips_sub_one_chip (c := qReducedConfig h_conn q D)
    _ = genus G - 1 := by rw [degree_max_superstable (qReducedConfig h_conn q D) h_max_cfg]
  have h_deg_eq : deg D = deg (qReducedRep h_conn q D) :=
    linear_equiv_preserves_deg G D (qReducedRep h_conn q D) (qReducedRep_spec h_conn q D).1
  rw [h_deg_eq, h_deg_D']
