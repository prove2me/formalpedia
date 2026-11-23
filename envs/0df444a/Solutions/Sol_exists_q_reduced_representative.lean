-- Prove2me | solution 1 for exists_q_reduced_representative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:49:25.620145+00:00
-- url     : https://prove2.me/submissions/3f903b81-6c59-4fb0-9521-1b3b6a90b819

module
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Data.Matrix.Mul
public import Definitions.Def_ChipFiringWithLean_Basic
public import Theorems.Thm_q_effective_exists
public import Theorems.Thm_q_effective_to_q_reduced

set_option autoImplicit true
@[expose] public section
public section
universe u
open Multiset Finset
attribute [instance] CFGraph.instDecidableEq CFGraph.instFintype CFGraph.instNonempty
open Matrix
theorem _root_.solution {G : CFGraph} (h_conn : graph_connected G) (q : G.V) (D : CFDiv G) :
  ∃ D' : CFDiv G, linear_equiv G D D' ∧ q_reduced G q D' :=
by
  rcases q_effective_exists h_conn q D with ⟨D_eff, h_eff, h_equiv⟩
  rcases q_effective_to_q_reduced h_conn h_eff with ⟨D_qred, h_qred, h_lequiv'⟩
  use D_qred
  constructor
  · -- Show linear equivalence
    exact h_equiv.trans h_lequiv'
  · -- Show q-reduced property
    exact h_qred
