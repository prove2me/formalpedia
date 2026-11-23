-- Prove2me | solution 1 for set_firing_eq_add_prin_indicator_script
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:44:00.690817+00:00
-- url     : https://prove2.me/submissions/ee61d858-b214-4083-ac6e-e972ab117db1

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
theorem _root_.solution (G : CFGraph) (D : CFDiv G)
    (S : Finset G.V) :
    set_firing G D S = D + prin G (indicator_script G S) := by
  classical
  funext v
  by_cases hv : v ∈ S
  · simp [set_firing, indicator_script, prin_apply, outdeg_S, hv]
    simp only [sub_mul, one_mul]
    rw [Finset.sum_sub_distrib]
    have hs : S.sum (fun x => (num_edges G v x : ℤ)) =
        (univ : Finset G.V).sum (fun x =>
          (if x ∈ S then 1 else 0) * (num_edges G v x : ℤ)) := by simp
    rw [← hs]
    ring
  · simp [set_firing, indicator_script, prin_apply, outdeg_S, hv]
