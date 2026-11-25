-- Prove2me | Theorems.Thm_BayesianPersuasion_Proof_senderPayoff_upperSemicontinuous
-- name    : BayesianPersuasion.Proof.senderPayoff_upperSemicontinuous
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T08:57:43.037369+00:00
-- url     : https://prove2.me/theorems/5c96b702-ad79-48a4-8956-ce9ad0033e85
-- title:
--   Proof: sender Payoff upper Semicontinuous
-- statement:
--   The Proof construction uses the sender Payoff upper Semicontinuous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/bayesian-persuasion-lean/blob/6bb350283717128bcd625daf93da18fe199e13d9/BayesianPersuasion/Primitives.lean#L110-L128
-- source:
--   https://github.com/Arthur742Ramos/bayesian-persuasion-lean/blob/6bb350283717128bcd625daf93da18fe199e13d9/BayesianPersuasion/Primitives.lean#L110-L128

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

theorem BayesianPersuasion.Proof.senderPayoff_upperSemicontinuous (u v : A → Ω → ℝ)
    (hu : ∀ ω, Continuous (fun a => u a ω))
    (hv : ∀ ω, Continuous (fun a => v a ω)) :
    UpperSemicontinuous (senderPayoff u v) := by sorry
