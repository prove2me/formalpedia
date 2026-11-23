-- Prove2me | solution 1 for eff_degree_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:43:10.414038+00:00
-- url     : https://prove2.me/submissions/00cea1bb-6bf3-45fb-a60c-a6ab9ecd5f80

module
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Data.Matrix.Mul
public import Definitions.Def_ChipFiringWithLean_Basic
public import Theorems.Thm_deg_one_chip
attribute [local simp] deg_one_chip

set_option autoImplicit true
@[expose] public section
public section
universe u
open Multiset Finset
attribute [instance] CFGraph.instDecidableEq CFGraph.instFintype CFGraph.instNonempty
theorem _root_.solution (D : CFDiv G) : effective D → deg D = 0 → D = 0 := by
  intro h_eff h_deg
  funext v
  exact (Finset.sum_eq_zero_iff_of_nonneg (fun w _ => h_eff w)).1
    (by simpa only [deg, AddMonoidHom.coe_mk, ZeroHom.coe_mk] using h_deg) v (Finset.mem_univ v)
