-- Prove2me | solution 1 for outdeg_S_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:43:48.932719+00:00
-- url     : https://prove2.me/submissions/575cbcf5-5ffc-44e0-bbf3-ef85bcb4e970

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
theorem _root_.solution (G : CFGraph) (S : Finset G.V) (v : G.V) :
    0 ≤ outdeg_S G S v := by
  unfold outdeg_S
  exact Finset.sum_nonneg fun _ _ => Int.natCast_nonneg _
