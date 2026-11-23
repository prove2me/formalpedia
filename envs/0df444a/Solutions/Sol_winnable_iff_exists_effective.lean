-- Prove2me | solution 1 for winnable_iff_exists_effective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:49:37.352604+00:00
-- url     : https://prove2.me/submissions/a7ed6ef4-45ec-4ec1-9d82-49b3808a1f27

module
public import Definitions.Def_ChipFiringWithLean_Basic
public import Definitions.Def_ChipFiringWithLean_Rank
public import Theorems.Thm_deg_one_chip
public import Theorems.Thm_legal_set_empty
attribute [local simp] deg_one_chip
attribute [local simp] legal_set_empty



set_option autoImplicit true
@[expose] public section
public section
set_option trace.split.failure true
open Multiset Finset
theorem _root_.solution (G : CFGraph) (D : CFDiv G) :
  winnable G D ↔ ∃ D' : CFDiv G, effective D' ∧ linear_equiv G D D' := by
  simp only [winnable, mem_Eff]
