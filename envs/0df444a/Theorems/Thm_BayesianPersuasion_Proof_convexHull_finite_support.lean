-- Prove2me | Theorems.Thm_BayesianPersuasion_Proof_convexHull_finite_support
-- name    : BayesianPersuasion.Proof.convexHull_finite_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:03:52.061676+00:00
-- url     : https://prove2.me/theorems/1f9656a7-3cea-4ceb-8645-3adc4b930b42
-- title:
--   Proof: convex Hull finite support
-- statement:
--   The Proof construction uses the convex Hull finite support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/bayesian-persuasion-lean/blob/6bb350283717128bcd625daf93da18fe199e13d9/BayesianPersuasion/CompactHull.lean#L27-L37
-- source:
--   https://github.com/Arthur742Ramos/bayesian-persuasion-lean/blob/6bb350283717128bcd625daf93da18fe199e13d9/BayesianPersuasion/CompactHull.lean#L27-L37

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

theorem BayesianPersuasion.Proof.convexHull_finite_support {s : Set E} {x : E} (hx : x ∈ convexHull ℝ s) :
    ∃ (k : ℕ) (_ : k ≤ Module.finrank ℝ E + 1) (z : Fin k → E) (w : Belief (Fin k)),
      (∀ j, z j ∈ s) ∧ ∑ j, w.val j • z j = x := by sorry
