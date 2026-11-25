-- Prove2me | Theorems.Thm_BayesianPersuasion_Proof_bestReply_graph_isClosed
-- name    : BayesianPersuasion.Proof.bestReply_graph_isClosed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T08:57:45.457319+00:00
-- url     : https://prove2.me/theorems/a24ce319-da52-4a99-b477-fc77d9d19032
-- title:
--   Proof: best Reply graph is Closed
-- statement:
--   The Proof construction uses the best Reply graph is Closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/bayesian-persuasion-lean/blob/6bb350283717128bcd625daf93da18fe199e13d9/BayesianPersuasion/Primitives.lean#L65-L71
-- source:
--   https://github.com/Arthur742Ramos/bayesian-persuasion-lean/blob/6bb350283717128bcd625daf93da18fe199e13d9/BayesianPersuasion/Primitives.lean#L65-L71

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

theorem BayesianPersuasion.Proof.bestReply_graph_isClosed (u : A → Ω → ℝ)
    (hu : ∀ ω, Continuous (fun a => u a ω)) :
    IsClosed {x : Belief Ω × A | BestReply u x.1 x.2} := by sorry
