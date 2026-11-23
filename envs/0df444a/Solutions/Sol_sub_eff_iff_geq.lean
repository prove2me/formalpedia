-- Prove2me | solution 1 for sub_eff_iff_geq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:44:03.478508+00:00
-- url     : https://prove2.me/submissions/de7d092c-da54-423f-996e-6cb688c0f255

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
theorem _root_.solution {G : CFGraph} (D₁ D₂ : CFDiv G) : effective (D₁ - D₂) ↔ D₁ ≥ D₂ :=
  forall_congr' (fun _ => sub_nonneg)
