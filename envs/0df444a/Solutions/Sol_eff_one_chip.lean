-- Prove2me | solution 1 for eff_one_chip
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:42:18.345572+00:00
-- url     : https://prove2.me/submissions/0569cb91-3bb1-4abc-b0b6-29547b84ec5c

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
theorem _root_.solution {G : CFGraph} (v : G.V) : effective (one_chip v) := by
  intro w
  dsimp only [one_chip]
  by_cases h_eq : w = v <;> simp only [h_eq, ↓reduceIte, ge_iff_le, Std.le_refl, zero_le_one]
