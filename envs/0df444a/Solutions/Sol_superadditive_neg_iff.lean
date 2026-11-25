-- Prove2me | solution 1 for superadditive_neg_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:27:14.146292+00:00
-- url     : https://prove2.me/submissions/ebaa3c03-0da6-4007-a79b-6066fde75f26

module
public import Mathlib.Analysis.Subadditive
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Definitions.Def_Fekete_Superadditive
public import Theorems.Thm_Subadditive_superadditive_neg
public import Theorems.Thm_Superadditive_subadditive_neg

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Filter Set
open scoped Topology
theorem _root_.solution {u : ℕ → ℝ} : (Superadditive fun n ↦ -u n) ↔ Subadditive u :=
  ⟨fun h ↦ by simpa using h.subadditive_neg, Subadditive.superadditive_neg⟩
