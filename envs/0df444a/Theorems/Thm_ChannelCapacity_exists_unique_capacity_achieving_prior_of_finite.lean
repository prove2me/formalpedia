-- Prove2me | Theorems.Thm_ChannelCapacity_exists_unique_capacity_achieving_prior_of_finite
-- name    : ChannelCapacity.exists_unique_capacity_achieving_prior_of_finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:42:38.934239+00:00
-- url     : https://prove2.me/theorems/ce70d9f5-e186-44a0-9ba8-f6c75f1fad40
-- title:
--   Channel Capacity: exists unique capacity achieving prior of finite
-- statement:
--   Finite-alphabet capacity theorem with all hypotheses discharged internally. The general
--   measure-theoretic theorem remains available separately; this theorem is the concrete upstream-ready
--   specialization using the canonical weak topology on probability measures over finite discrete
--   alphabets.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Finite.lean#L632-L647
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Finite.lean#L632-L647

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

theorem ChannelCapacity.exists_unique_capacity_achieving_prior_of_finite [Finite β]
    [Nonempty α] (k : Kernel α β) [IsMarkovKernel k]
    (hRank : ChannelCapacity.Kernel.RowMatrixFullRank k) :
    ∃! p : ProbabilityMeasure α, mutualInformation p k = channelCapacity k := by sorry
