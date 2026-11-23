-- Prove2me | solution 1 for set_firing_apply_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:42:34.42189+00:00
-- url     : https://prove2.me/submissions/abbacbd4-3c42-4722-9e42-6fd8adc922bc

module
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Data.Matrix.Mul
public import Definitions.Def_ChipFiringWithLean_Basic

set_option autoImplicit true
@[expose] public section
public section
universe u
open Multiset Finset
attribute [instance] CFGraph.instDecidableEq CFGraph.instFintype CFGraph.instNonempty
theorem _root_.solution (G : CFGraph) (D : CFDiv G) {S : Finset G.V}
    {v : G.V} (hv : v ∈ S) :
    set_firing G D S v = D v - outdeg_S G S v := by
  simp [set_firing, hv]
