-- Prove2me | Theorems.Thm_ChannelCapacity_klDiv_mutualInformation_chain
-- name    : ChannelCapacity.klDiv_mutualInformation_chain
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:39:59.527026+00:00
-- url     : https://prove2.me/theorems/ddcb8eb2-8445-499e-861a-84ae90d300f4
-- title:
--   Channel Capacity: kl Div mutual Information chain
-- statement:
--   The Channel Capacity construction uses the kl Div mutual Information chain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/ChainRule.lean#L33-L100
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/ChainRule.lean#L33-L100

module
public import Definitions.Def_LeanPool_ChannelCapacity_Basic
public import Definitions.Def_LeanPool_ChannelCapacity_KernelCompositionKullbackLeibler
public import Mathlib.InformationTheory.KullbackLeibler.ChainRule
public import Mathlib.Probability.Kernel.Posterior
public import Definitions.Def_LeanPool_ChannelCapacity_ChainRule
set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open ChannelCapacity
open InformationTheory

theorem ChannelCapacity.klDiv_mutualInformation_chain
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [StandardBorelSpace α] [Nonempty α]
    (k : Kernel α β) [IsMarkovKernel k] (p : ProbabilityMeasure α) (ν : Measure β)
    [IsFiniteMeasure ν] :
    klDiv (jointLaw k p).toMeasure (p.toMeasure ⊗ₘ Kernel.const α ν) =
      klDiv (jointLaw k p).toMeasure (independentJointLaw k p).toMeasure +
        klDiv (outputPrior k p).toMeasure ν := by sorry
