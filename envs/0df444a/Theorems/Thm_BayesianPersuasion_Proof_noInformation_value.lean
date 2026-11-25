-- Prove2me | Theorems.Thm_BayesianPersuasion_Proof_noInformation_value
-- name    : BayesianPersuasion.Proof.noInformation_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:07:52.059492+00:00
-- url     : https://prove2.me/theorems/6af296c8-8bd7-406b-beb3-442c299612ba
-- title:
--   Proof: no Information value
-- statement:
--   The Proof construction uses the no Information value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/bayesian-persuasion-lean/blob/6bb350283717128bcd625daf93da18fe199e13d9/BayesianPersuasion/Attainment.lean#L59-L69
-- source:
--   https://github.com/Arthur742Ramos/bayesian-persuasion-lean/blob/6bb350283717128bcd625daf93da18fe199e13d9/BayesianPersuasion/Attainment.lean#L59-L69

module
public import Definitions.Def_BayesianPersuasion_Signals
public import Definitions.Def_BayesianPersuasion_CompactHull
public import Mathlib.Analysis.Convex.Jensen
public import Definitions.Def_BayesianPersuasion_Attainment
set_option autoImplicit true
@[expose] public section
public section
universe uΩ uA
open Set Finset
open BayesianPersuasion
variable {Ω : Type uΩ} {A : Type uA} [Fintype Ω]
open BayesianPersuasion.Proof

theorem BayesianPersuasion.Proof.noInformation_value (u v : A → Ω → ℝ) (p : Belief Ω) :
    signalValue u v p noInformationSignal = senderPayoff u v p := by sorry
