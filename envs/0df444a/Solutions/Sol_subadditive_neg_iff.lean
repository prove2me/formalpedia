-- Prove2me | solution 1 for subadditive_neg_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:27:50.25284+00:00
-- url     : https://prove2.me/submissions/07cdeaa1-b77a-4f4a-a65c-e321a83f463e

module
public import Mathlib.Analysis.Subadditive
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Definitions.Def_Fekete_Superadditive
public import Theorems.Thm_Subadditive_superadditive_neg
public import Theorems.Thm_Superadditive_subadditive_neg
public import Theorems.Thm_superadditive_neg_iff
attribute [local simp] superadditive_neg_iff

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Filter Set
open scoped Topology
theorem _root_.solution {u : ℕ → ℝ} : (Subadditive fun n ↦ -u n) ↔ Superadditive u :=
  ⟨fun h ↦ by simpa using h.superadditive_neg, Superadditive.subadditive_neg⟩
