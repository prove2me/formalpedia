-- Prove2me | Theorems.Thm_ChannelCapacity_klFun_singletonMass
-- name    : ChannelCapacity.klFun_singletonMass
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:42:13.266833+00:00
-- url     : https://prove2.me/theorems/c491f390-a6fd-495f-bad6-fb755bbcc904
-- title:
--   Channel Capacity: kl Fun singleton Mass
-- statement:
--   The Channel Capacity construction uses the kl Fun singleton Mass property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Finite.lean#L80-L84
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Finite.lean#L80-L84

module
public import Definitions.Def_LeanPool_ChannelCapacity_Capacity
public import Definitions.Def_LeanPool_ChannelCapacity_ChainRule
public import Definitions.Def_LeanPool_ChannelCapacity_KernelCompositionKullbackLeibler
public import Definitions.Def_LeanPool_ChannelCapacity_StrictConcavity
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Definitions.Def_LeanPool_ChannelCapacity_Finite
set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory
open ProbabilityTheory
open scoped BigOperators ENNReal
open ChannelCapacity
variable {α β : Type*} [Fintype α] [Fintype β] [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β]
omit [Fintype α] [MeasurableSingletonClass α]

theorem ChannelCapacity.klFun_singletonMass (μ : ProbabilityMeasure α) (a : α) :
    InformationTheory.klFun ((μ.toMeasure {a}).toReal) =
      1 - (μ.toMeasure {a}).toReal - Real.negMulLog ((μ.toMeasure {a}).toReal) := by sorry
