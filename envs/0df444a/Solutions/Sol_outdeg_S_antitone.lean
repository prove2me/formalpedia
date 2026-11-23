-- Prove2me | solution 1 for outdeg_S_antitone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:43:50.882799+00:00
-- url     : https://prove2.me/submissions/860fb274-a059-4a5c-963d-47032276411d

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
theorem _root_.solution (G : CFGraph) {S T : Finset G.V} (h : S ⊆ T) (v : G.V) :
    outdeg_S G T v ≤ outdeg_S G S v := by
  unfold outdeg_S
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.compl_subset_compl.mpr h)
    (fun _ _ _ => Int.natCast_nonneg _)
