-- Prove2me | solution 1 for num_edges_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:42:02.262875+00:00
-- url     : https://prove2.me/submissions/8a902988-a231-4da2-98b1-d2d8197f0853

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
theorem _root_.solution (G : CFGraph) (v w : G.V) :
  num_edges G v w = num_edges G w v := by
  simp only [num_edges, Or.comm]
