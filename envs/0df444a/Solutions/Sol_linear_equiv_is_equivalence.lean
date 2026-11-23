-- Prove2me | solution 1 for linear_equiv_is_equivalence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:49:14.11183+00:00
-- url     : https://prove2.me/submissions/21db9df7-d1ce-4c3a-8ea8-38efa2ca87e7

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
theorem _root_.solution (G : CFGraph) : Equivalence (linear_equiv G) :=
  ⟨linear_equiv.refl G, linear_equiv.symm, linear_equiv.trans⟩
