-- Prove2me | Theorems.Thm_BayesianPersuasion_Proof_senderPayoff_measurable
-- name    : BayesianPersuasion.Proof.senderPayoff_measurable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:08:12.341795+00:00
-- url     : https://prove2.me/theorems/ed934cb2-b7a3-5867-806f-86ad85e4f954
-- title:
--   Proof: sender Payoff measurable
-- statement:
--   The Proof construction uses the sender Payoff measurable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/bayesian-persuasion-lean/blob/6bb350283717128bcd625daf93da18fe199e13d9/BayesianPersuasion/Theorems.lean#L87-L89
-- source:
--   https://github.com/Arthur742Ramos/bayesian-persuasion-lean/blob/6bb350283717128bcd625daf93da18fe199e13d9/BayesianPersuasion/Theorems.lean#L87-L89

module
public import Definitions.Def_BayesianPersuasion_Attainment
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Definitions.Def_BayesianPersuasion_Theorems
set_option autoImplicit true
@[expose] public section
public section
universe uΩ uA
open Set Finset
open BayesianPersuasion
variable {Ω : Type uΩ} {A : Type uA} [Fintype Ω] [Nonempty Ω]
variable [MetricSpace A] [CompactSpace A] [Nonempty A]
variable (u v : A → Ω → ℝ)
variable (hu : ∀ ω, Continuous (fun a => u a ω))
variable (hv : ∀ ω, Continuous (fun a => v a ω))
open BayesianPersuasion.Proof
include hu hv

theorem BayesianPersuasion.Proof.senderPayoff_measurable [MeasurableSpace (Belief Ω)] [BorelSpace (Belief Ω)] :
    Measurable (senderPayoff u v) := by sorry
