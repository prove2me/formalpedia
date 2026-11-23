-- Prove2me | solution 1 for q_reduced_superstable_correspondence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:48:19.734801+00:00
-- url     : https://prove2.me/submissions/c9084215-7117-4ed1-acff-5fe8c8ec82e1

module
public import Definitions.Def_ChipFiringWithLean_Basic
public import Definitions.Def_ChipFiringWithLean_Config
public import Theorems.Thm_superstable_iff_q_reduced
public import Theorems.Thm_q_reduced_toConfig_superstable

set_option autoImplicit true
@[expose] public section
public section
set_option trace.split.failure true
open Multiset Finset
theorem _root_.solution (G : CFGraph) (q : G.V) (D : CFDiv G) :
  q_reduced G q D ↔ ∃ c : Config G q, superstable G q c ∧
  D = toDiv (deg D) c := by
  constructor
  . -- Forward direction (q_reduced → ∃ c, superstable ∧ D = c - δ_q)
    intro h_qred
    refine ⟨toConfig ⟨D, h_qred.1⟩, q_reduced_toConfig_superstable G q D h_qred, ?_⟩
    exact (q_reduced_toDiv_toConfig G q D h_qred).symm
  -- Backward direction (∃ c, superstable ∧ D = c - δ_q → q_reduced)
  · intro h_exists
    rcases h_exists with ⟨c, h_super, D_eq⟩
    rw [D_eq]
    rw [← superstable_iff_q_reduced G q (deg D) c]
    exact h_super
