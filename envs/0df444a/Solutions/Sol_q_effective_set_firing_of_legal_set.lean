-- Prove2me | solution 1 for q_effective_set_firing_of_legal_set
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:48:21.18713+00:00
-- url     : https://prove2.me/submissions/8247992e-0908-4340-aeea-26f87d5dca76

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
theorem _root_.solution (G : CFGraph) {q : G.V} {D : CFDiv G}
    {S : Finset G.V} (hD : q_effective q D) (hS : legal_set G D S) :
    q_effective q (set_firing G D S) := by
  intro v hvq
  by_cases hv : v ∈ S
  · rw [set_firing_apply_of_mem G D hv]
    exact sub_nonneg.mpr (hS v hv)
  · exact le_trans (hD v hvq) (le_set_firing_apply_of_not_mem G D hv)
