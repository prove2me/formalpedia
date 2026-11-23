-- Prove2me | solution 1 for le_set_firing_apply_of_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:44:33.743825+00:00
-- url     : https://prove2.me/submissions/7a9d7a22-6ba0-4e8a-9540-679765cd13d1

module
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Data.Matrix.Mul
public import Definitions.Def_ChipFiringWithLean_Basic
public import Theorems.Thm_outdeg_S_nonneg
public import Theorems.Thm_set_firing_apply_of_not_mem

set_option autoImplicit true
@[expose] public section
public section
universe u
open Multiset Finset
attribute [instance] CFGraph.instDecidableEq CFGraph.instFintype CFGraph.instNonempty
theorem _root_.solution (G : CFGraph) (D : CFDiv G)
    {S : Finset G.V} {v : G.V} (hv : v ∉ S) :
    D v ≤ set_firing G D S v := by
  rw [set_firing_apply_of_not_mem G D hv]
  exact le_add_of_nonneg_right (outdeg_S_nonneg G Sᶜ v)
