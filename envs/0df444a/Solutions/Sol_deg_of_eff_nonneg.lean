-- Prove2me | solution 1 for deg_of_eff_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:44:04.535044+00:00
-- url     : https://prove2.me/submissions/14c859ad-f5ac-40f1-bacf-c52585d5aa34

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
theorem _root_.solution (D : CFDiv G) :
  effective D → deg D ≥ 0 := by
  intro h_eff
  exact Finset.sum_nonneg fun v _ => h_eff v
