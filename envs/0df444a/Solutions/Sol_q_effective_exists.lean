-- Prove2me | solution 1 for q_effective_exists
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:48:20.776854+00:00
-- url     : https://prove2.me/submissions/a688a799-f98f-4b2f-8656-a0d6e5a8a94e

module
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Data.Matrix.Mul
public import Definitions.Def_ChipFiringWithLean_Basic
public import Theorems.Thm_deg_one_chip
public import Theorems.Thm_benevolent_of_nonempty
attribute [local simp] deg_one_chip

set_option autoImplicit true
@[expose] public section
public section
universe u
open Multiset Finset
attribute [instance] CFGraph.instDecidableEq CFGraph.instFintype CFGraph.instNonempty
open Matrix
theorem _root_.solution {G : CFGraph} (h_conn : graph_connected G) (q : G.V) (D : CFDiv G) :
  ∃ (E : CFDiv G), q_effective q E ∧ linear_equiv G D E := by
  have h_bene := benevolent_of_nonempty h_conn {q} (by use q; simp only [Finset.mem_singleton]) D
  rcases h_bene with ⟨E,h_equiv, h_eff⟩
  have : q_effective q E := by
    intro v v_ne_q
    specialize h_eff v
    contrapose! h_eff
    simp only [h_eff, Finset.mem_singleton, true_and]
    exact v_ne_q
  exact ⟨E,this, h_equiv⟩
