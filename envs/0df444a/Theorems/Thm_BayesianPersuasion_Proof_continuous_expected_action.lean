-- Prove2me | Theorems.Thm_BayesianPersuasion_Proof_continuous_expected_action
-- name    : BayesianPersuasion.Proof.continuous_expected_action
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T08:57:45.676306+00:00
-- url     : https://prove2.me/theorems/dfeb7a45-c070-495a-9d10-54c9809fa554
-- title:
--   Proof: continuous expected action
-- statement:
--   The Proof construction uses the continuous expected action property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/bayesian-persuasion-lean/blob/6bb350283717128bcd625daf93da18fe199e13d9/BayesianPersuasion/Primitives.lean#L53-L56
-- source:
--   https://github.com/Arthur742Ramos/bayesian-persuasion-lean/blob/6bb350283717128bcd625daf93da18fe199e13d9/BayesianPersuasion/Primitives.lean#L53-L56

module
public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Topology.Order.Compact
public import Definitions.Def_BayesianPersuasion_Primitives
set_option autoImplicit true
@[expose] public section
public section
universe uΩ uA
open Set Finset
open BayesianPersuasion
variable (Ω : Type uΩ) [Fintype Ω]
variable {Ω} {A : Type uA}
open BayesianPersuasion.Proof
variable [TopologicalSpace A]

theorem BayesianPersuasion.Proof.continuous_expected_action (u : A → Ω → ℝ)
    (hu : ∀ ω, Continuous (fun a => u a ω)) (p : Belief Ω) :
    Continuous (expected u p) := by sorry
