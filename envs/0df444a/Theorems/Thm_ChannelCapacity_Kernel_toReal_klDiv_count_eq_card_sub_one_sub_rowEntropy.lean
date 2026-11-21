-- Prove2me | Theorems.Thm_ChannelCapacity_Kernel_toReal_klDiv_count_eq_card_sub_one_sub_rowEntropy
-- name    : ChannelCapacity.Kernel.toReal_klDiv_count_eq_card_sub_one_sub_rowEntropy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:41:56.969404+00:00
-- url     : https://prove2.me/theorems/56580433-08e7-4458-9c8e-9f0db2b898dd
-- title:
--   Kernel: to Real kl Div count eq card sub one sub row Entropy
-- statement:
--   The KL divergence of a kernel row against counting measure is the usual finite entropy
--   expression.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Finite.lean#L149-L154
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Finite.lean#L149-L154

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

theorem ChannelCapacity.Kernel.toReal_klDiv_count_eq_card_sub_one_sub_rowEntropy
    (k : Kernel α β) [IsMarkovKernel k] (a : α) :
    (InformationTheory.klDiv (k a) Measure.count).toReal =
      (Fintype.card β : ℝ) - 1 - Kernel.rowEntropy k a := by sorry
