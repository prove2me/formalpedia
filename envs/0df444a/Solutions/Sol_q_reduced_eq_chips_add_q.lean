-- Prove2me | solution 1 for q_reduced_eq_chips_add_q
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:45:49.720776+00:00
-- url     : https://prove2.me/submissions/5c1062ea-8d02-42b9-912c-f57e951cb874

module
public import Definitions.Def_ChipFiringWithLean_Basic
public import Definitions.Def_ChipFiringWithLean_Config
public import Theorems.Thm_deg_one_chip
public import Theorems.Thm_legal_set_empty
attribute [local simp] deg_one_chip
attribute [local simp] legal_set_empty



set_option autoImplicit true
@[expose] public section
public section
set_option trace.split.failure true
open Multiset Finset
theorem _root_.solution (G : CFGraph) (q : G.V) (D : CFDiv G)
    (h_qred : q_reduced G q D) :
    D = (toConfig ⟨D, h_qred.1⟩).chips + D q • one_chip q := by
  let c : Config G q := toConfig ⟨D, h_qred.1⟩
  have h_deg : deg D = config_degree c + D q := by
    simpa only [add_comm] using (config_degree_div_degree ⟨D, h_qred.1⟩)
  calc
    D = toDiv (deg D) c := by
      exact (q_reduced_toDiv_toConfig G q D h_qred).symm
    _ = toDiv (config_degree c + D q) c := by rw [h_deg]
    _ = c.chips + D q • one_chip q := toDiv_config_degree_add c (D q)
