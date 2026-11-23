-- Prove2me | solution 1 for set_firing_apply_of_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:43:52.394058+00:00
-- url     : https://prove2.me/submissions/75fa6975-84a1-438a-af09-0e463559de7a

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
theorem _root_.solution (G : CFGraph) (D : CFDiv G)
    {S : Finset G.V} {v : G.V} (hv : v ∉ S) :
    set_firing G D S v = D v + outdeg_S G Sᶜ v := by
  simp [set_firing, hv]
