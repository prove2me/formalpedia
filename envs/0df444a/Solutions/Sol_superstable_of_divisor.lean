-- Prove2me | solution 1 for superstable_of_divisor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:53:07.271926+00:00
-- url     : https://prove2.me/submissions/5ba8d6b8-635a-4baa-94ef-6077a0276e13

module
public import Definitions.Def_ChipFiringWithLean_Orientation
public import Definitions.Def_ChipFiringWithLean_Rank
public import Definitions.Def_ChipFiringWithLean_RRGHelpers
public import Theorems.Thm_deg_one_chip
public import Theorems.Thm_legal_set_empty
public import Theorems.Thm_q_reduced_eq_chips_add_q
public import Theorems.Thm_q_reduced_toConfig_superstable
attribute [local simp] deg_one_chip
attribute [local simp] legal_set_empty


section
@[expose] public section
set_option trace.split.failure true
open Multiset Finset
private lemma qReducedConfig_superstable {G : CFGraph}
    (h_conn : graph_connected G) (q : G.V) (D : CFDiv G) :
    superstable G q (qReducedConfig h_conn q D) := by
  exact q_reduced_toConfig_superstable G q (qReducedRep h_conn q D) (qReducedRep_spec h_conn q D).2
end
end

set_option autoImplicit true
@[expose] public section
public section
set_option trace.split.failure true
open Multiset Finset
theorem _root_.solution {G : CFGraph} (h_conn : graph_connected G) (q : G.V) (D : CFDiv G) :
  ∃ (c : Config G q) (k : ℤ),
    linear_equiv G D (c.chips + k • (one_chip q)) ∧
    superstable G q c := by
  let D' := qReducedRep h_conn q D
  let c := qReducedConfig h_conn q D
  use c, D' q
  constructor
  ·
    have h := (qReducedRep_spec h_conn q D).1
    rw [q_reduced_eq_chips_add_q G q (qReducedRep h_conn q D) (qReducedRep_spec h_conn q D).2] at h
    exact h
  ·
    simpa only using qReducedConfig_superstable h_conn q D
