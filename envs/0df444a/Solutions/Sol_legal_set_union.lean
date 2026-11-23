-- Prove2me | solution 1 for legal_set_union
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:49:15.098861+00:00
-- url     : https://prove2.me/submissions/692855ec-5b19-4466-bc5c-ee36dda73839

module
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Data.Matrix.Mul
public import Definitions.Def_ChipFiringWithLean_Basic
public import Theorems.Thm_outdeg_S_antitone

set_option autoImplicit true
@[expose] public section
public section
universe u
open Multiset Finset
attribute [instance] CFGraph.instDecidableEq CFGraph.instFintype CFGraph.instNonempty
open Matrix
theorem _root_.solution (G : CFGraph) {D : CFDiv G} {S T : Finset G.V}
    (hS : legal_set G D S) (hT : legal_set G D T) :
    legal_set G D (S ∪ T) := by
  intro v hv
  rcases Finset.mem_union.mp hv with hv | hv
  · exact le_trans (outdeg_S_antitone G Finset.subset_union_left v) (hS v hv)
  · exact le_trans (outdeg_S_antitone G Finset.subset_union_right v) (hT v hv)
