-- Prove2me | solution 1 for unique_q_reduced
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:50:02.468181+00:00
-- url     : https://prove2.me/submissions/c9e77a4b-b947-4ce6-b7d1-e097dbe64e43

module
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Data.Matrix.Mul
public import Definitions.Def_ChipFiringWithLean_Basic
public import Theorems.Thm_q_reduced_unique
public import Theorems.Thm_exists_q_reduced_representative

set_option autoImplicit true
@[expose] public section
public section
universe u
open Multiset Finset
attribute [instance] CFGraph.instDecidableEq CFGraph.instFintype CFGraph.instNonempty
open Matrix
theorem _root_.solution {G : CFGraph} (h_conn : graph_connected G) (q : G.V) (D : CFDiv G) :
  ∃! D' : CFDiv G, linear_equiv G D D' ∧ q_reduced G q D' := by
  -- Prove existence and uniqueness separately
  have h_exists : ∃ D' : CFDiv G, linear_equiv G D D' ∧ q_reduced G q D' := by
    exact exists_q_reduced_representative h_conn q D

  -- Combine existence and uniqueness using the standard constructor
  obtain ⟨D', hD'⟩ := h_exists
  refine ExistsUnique.intro D' hD' (fun y hy => ?_)
  exact q_reduced_unique G q y D' ⟨hy.2, hD'.2, hy.1.symm.trans hD'.1⟩
