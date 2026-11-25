-- Prove2me | Theorems.Thm_BayesianPersuasion_Proof_compact_convexHull
-- name    : BayesianPersuasion.Proof.compact_convexHull
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:05:58.422982+00:00
-- url     : https://prove2.me/theorems/e1fc3452-7bf9-45d6-b076-2be5c04f7324
-- title:
--   Proof: compact convex Hull
-- statement:
--   Compact subsets of a finite dimensional real space have compact convex hull.
--
--   Source: https://github.com/Arthur742Ramos/bayesian-persuasion-lean/blob/6bb350283717128bcd625daf93da18fe199e13d9/BayesianPersuasion/CompactHull.lean#L81-L104
-- source:
--   https://github.com/Arthur742Ramos/bayesian-persuasion-lean/blob/6bb350283717128bcd625daf93da18fe199e13d9/BayesianPersuasion/CompactHull.lean#L81-L104

module
public import Definitions.Def_BayesianPersuasion_Primitives
public import Mathlib.Analysis.Convex.Caratheodory
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.Tactic
public import Definitions.Def_BayesianPersuasion_CompactHull
set_option autoImplicit true
@[expose] public section
public section
open Set Finset
open BayesianPersuasion BayesianPersuasion.Proof
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace E] [T2Space E] [ContinuousAdd E] [ContinuousSMul ℝ E]

theorem BayesianPersuasion.Proof.compact_convexHull {s : Set E} (hs : IsCompact s) : IsCompact (convexHull ℝ s) := by sorry
