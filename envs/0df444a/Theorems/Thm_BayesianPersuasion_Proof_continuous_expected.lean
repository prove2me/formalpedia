-- Prove2me | Theorems.Thm_BayesianPersuasion_Proof_continuous_expected
-- name    : BayesianPersuasion.Proof.continuous_expected
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T08:57:40.796388+00:00
-- url     : https://prove2.me/theorems/a176f0f0-5ce4-58a5-8069-1612789a9395
-- title:
--   Proof: continuous expected
-- statement:
--   The Proof construction uses the continuous expected property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/bayesian-persuasion-lean/blob/6bb350283717128bcd625daf93da18fe199e13d9/BayesianPersuasion/Primitives.lean#L46-L51
-- source:
--   https://github.com/Arthur742Ramos/bayesian-persuasion-lean/blob/6bb350283717128bcd625daf93da18fe199e13d9/BayesianPersuasion/Primitives.lean#L46-L51

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

theorem BayesianPersuasion.Proof.continuous_expected (u : A → Ω → ℝ) (hu : ∀ ω, Continuous (fun a => u a ω)) :
    Continuous (fun x : Belief Ω × A => expected u x.1 x.2) := by sorry
