-- Prove2me | solution 1 for q_reduced_toConfig_superstable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:46:33.648352+00:00
-- url     : https://prove2.me/submissions/a902d15e-2a57-4f3f-92de-acb464e22c10

module
public import Definitions.Def_ChipFiringWithLean_Basic
public import Definitions.Def_ChipFiringWithLean_Config
public import Theorems.Thm_superstable_iff_q_reduced
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
    superstable G q (toConfig ⟨D, h_qred.1⟩) := by
  rw [superstable_iff_q_reduced G q (deg D) (toConfig ⟨D, h_qred.1⟩)]
  simpa only [q_reduced_toDiv_toConfig G q D h_qred] using h_qred
