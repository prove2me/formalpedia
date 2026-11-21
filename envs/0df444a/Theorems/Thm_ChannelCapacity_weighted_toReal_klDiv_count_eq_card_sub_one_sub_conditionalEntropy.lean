-- Prove2me | Theorems.Thm_ChannelCapacity_weighted_toReal_klDiv_count_eq_card_sub_one_sub_conditionalEntropy
-- name    : ChannelCapacity.weighted_toReal_klDiv_count_eq_card_sub_one_sub_conditionalEntropy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:41:54.212877+00:00
-- url     : https://prove2.me/theorems/036941a5-ac84-432d-924b-d3cfc9d34aef
-- title:
--   Channel Capacity: weighted to Real kl Div count eq card sub one sub conditional Entropy
-- statement:
--   Averaging the row KL divergences against counting measure recovers the conditional entropy.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Finite.lean#L157-L179
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Finite.lean#L157-L179

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

theorem ChannelCapacity.weighted_toReal_klDiv_count_eq_card_sub_one_sub_conditionalEntropy
    (k : Kernel α β) [IsMarkovKernel k] (p : ProbabilityMeasure α) :
    ∑ a, (p.toMeasure {a}).toReal * (InformationTheory.klDiv (k a) Measure.count).toReal =
      (Fintype.card β : ℝ) - 1 - conditionalEntropy p k := by sorry
