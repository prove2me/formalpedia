-- Prove2me | solution 1 for deg_one_chip
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:41:59.766322+00:00
-- url     : https://prove2.me/submissions/5743d27c-043e-43ff-9d10-5a35c579939c

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
theorem _root_.solution {G : CFGraph} (v : G.V) : deg (one_chip v) = 1 := by
  simp only [deg, AddMonoidHom.coe_mk, ZeroHom.coe_mk, one_chip, sum_ite_eq', mem_univ, ↓reduceIte]
