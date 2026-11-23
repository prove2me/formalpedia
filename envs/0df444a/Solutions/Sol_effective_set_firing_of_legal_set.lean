-- Prove2me | solution 1 for effective_set_firing_of_legal_set
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:49:14.597195+00:00
-- url     : https://prove2.me/submissions/101b78a8-b17b-4986-9a62-d0b59de92dde

module
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Data.Matrix.Mul
public import Definitions.Def_ChipFiringWithLean_Basic
public import Theorems.Thm_set_firing_apply_of_mem
public import Theorems.Thm_le_set_firing_apply_of_not_mem

set_option autoImplicit true
@[expose] public section
public section
universe u
open Multiset Finset
attribute [instance] CFGraph.instDecidableEq CFGraph.instFintype CFGraph.instNonempty
open Matrix
theorem _root_.solution (G : CFGraph) {D : CFDiv G}
    {S : Finset G.V} (hD : effective D) (hS : legal_set G D S) :
    effective (set_firing G D S) := by
  intro v
  by_cases hv : v ∈ S
  · rw [set_firing_apply_of_mem G D hv]
    have h := hS v hv
    omega
  · exact le_trans (hD v) (le_set_firing_apply_of_not_mem G D hv)
