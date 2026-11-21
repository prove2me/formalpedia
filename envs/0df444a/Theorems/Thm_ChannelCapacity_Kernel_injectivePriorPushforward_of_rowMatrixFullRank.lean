-- Prove2me | Theorems.Thm_ChannelCapacity_Kernel_injectivePriorPushforward_of_rowMatrixFullRank
-- name    : ChannelCapacity.Kernel.injectivePriorPushforward_of_rowMatrixFullRank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:41:27.237183+00:00
-- url     : https://prove2.me/theorems/79b45ce9-c77f-474b-a59e-8dbb3f5c75b6
-- title:
--   Kernel: injective Prior Pushforward of row Matrix Full Rank
-- statement:
--   The Kernel construction uses the injective Prior Pushforward of row Matrix Full Rank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Finite.lean#L430-L458
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Finite.lean#L430-L458

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
omit [Fintype β]

theorem ChannelCapacity.Kernel.injectivePriorPushforward_of_rowMatrixFullRank
    (k : Kernel α β) [IsMarkovKernel k] (hRank : ChannelCapacity.Kernel.RowMatrixFullRank k) :
    Kernel.InjectivePriorPushforward k := by sorry
