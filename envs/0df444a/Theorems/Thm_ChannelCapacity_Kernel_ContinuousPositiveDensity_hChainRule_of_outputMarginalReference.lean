-- Prove2me | Theorems.Thm_ChannelCapacity_Kernel_ContinuousPositiveDensity_hChainRule_of_outputMarginalReference
-- name    : ChannelCapacity.Kernel.ContinuousPositiveDensity.hChainRule_of_outputMarginalReference
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:42:26.845183+00:00
-- url     : https://prove2.me/theorems/8f8b986b-5e5f-478b-abd4-bc9180bed8b4
-- title:
--   Continuous Positive Density: h Chain Rule of output Marginal Reference
-- statement:
--   The Continuous Positive Density construction uses the h Chain Rule of output Marginal Reference property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Discharged.lean#L369-L378
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Discharged.lean#L369-L378

module
public import Definitions.Def_LeanPool_ChannelCapacity_Capacity
public import Definitions.Def_LeanPool_ChannelCapacity_ChainRule
public import Definitions.Def_LeanPool_ChannelCapacity_KernelCompositionKullbackLeibler
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Definitions.Def_LeanPool_ChannelCapacity_Discharged
set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory
open ProbabilityTheory
open scoped ENNReal
open ChannelCapacity
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable [TopologicalSpace α] [TopologicalSpace β]
open ChannelCapacity.Kernel
open ChannelCapacity.Kernel.ContinuousPositiveDensity
variable {k : Kernel α β} [IsMarkovKernel k] [OpensMeasurableSpace α] {ν : Measure β}
variable [CompactSpace α] [CompactSpace β] [PolishSpace α] [PolishSpace β]
variable [BorelSpace α] [BorelSpace β]
variable [OpensMeasurableSpace β] [IsFiniteMeasure ν]
omit [TopologicalSpace β] [CompactSpace α] [CompactSpace β] [PolishSpace β] [BorelSpace β]
  [OpensMeasurableSpace α] [OpensMeasurableSpace β] [IsFiniteMeasure ν]

theorem ChannelCapacity.Kernel.ContinuousPositiveDensity.hChainRule_of_outputMarginalReference
    (p : ProbabilityMeasure α) (ν' : Measure β)
    (hRef : Kernel.OutputMarginalReference k p ν') :
    InformationTheory.klDiv (jointLaw k p).toMeasure (p.toMeasure ⊗ₘ Kernel.const _ ν') =
      InformationTheory.klDiv (jointLaw k p).toMeasure (independentJointLaw k p).toMeasure +
        InformationTheory.klDiv (outputPrior k p).toMeasure ν' := by sorry
