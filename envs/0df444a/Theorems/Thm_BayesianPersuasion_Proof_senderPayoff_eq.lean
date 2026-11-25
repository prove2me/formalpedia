-- Prove2me | Theorems.Thm_BayesianPersuasion_Proof_senderPayoff_eq
-- name    : BayesianPersuasion.Proof.senderPayoff_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T08:57:45.135156+00:00
-- url     : https://prove2.me/theorems/c480fcea-4495-42f0-9480-472992979abb
-- title:
--   Proof: sender Payoff eq
-- statement:
--   The Proof construction uses the sender Payoff eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/bayesian-persuasion-lean/blob/6bb350283717128bcd625daf93da18fe199e13d9/BayesianPersuasion/Primitives.lean#L91-L100
-- source:
--   https://github.com/Arthur742Ramos/bayesian-persuasion-lean/blob/6bb350283717128bcd625daf93da18fe199e13d9/BayesianPersuasion/Primitives.lean#L91-L100

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

theorem BayesianPersuasion.Proof.senderPayoff_eq (u v : A → Ω → ℝ)
    (hu : ∀ ω, Continuous (fun a => u a ω))
    (hv : ∀ ω, Continuous (fun a => v a ω)) (p : Belief Ω) {a : A}
    (ha : SenderPreferred u v p a) : senderPayoff u v p = expected v p a := by sorry
