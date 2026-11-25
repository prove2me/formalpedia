-- Prove2me | Theorems.Thm_BayesianPersuasion_Proof_bestReply_le_senderPayoff
-- name    : BayesianPersuasion.Proof.bestReply_le_senderPayoff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T08:57:42.85662+00:00
-- url     : https://prove2.me/theorems/37159c7f-7fea-58bd-a2ba-13033cb11135
-- title:
--   Proof: best Reply le sender Payoff
-- statement:
--   The Proof construction uses the best Reply le sender Payoff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/bayesian-persuasion-lean/blob/6bb350283717128bcd625daf93da18fe199e13d9/BayesianPersuasion/Primitives.lean#L102-L108
-- source:
--   https://github.com/Arthur742Ramos/bayesian-persuasion-lean/blob/6bb350283717128bcd625daf93da18fe199e13d9/BayesianPersuasion/Primitives.lean#L102-L108

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
variable [CompactSpace A] [Nonempty A]

theorem BayesianPersuasion.Proof.bestReply_le_senderPayoff (u v : A → Ω → ℝ)
    (hu : ∀ ω, Continuous (fun a => u a ω))
    (hv : ∀ ω, Continuous (fun a => v a ω)) (p : Belief Ω) {a : A}
    (ha : BestReply u p a) : expected v p a ≤ senderPayoff u v p := by sorry
