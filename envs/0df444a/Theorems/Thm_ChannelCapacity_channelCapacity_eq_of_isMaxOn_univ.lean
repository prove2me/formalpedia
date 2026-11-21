-- Prove2me | Theorems.Thm_ChannelCapacity_channelCapacity_eq_of_isMaxOn_univ
-- name    : ChannelCapacity.channelCapacity_eq_of_isMaxOn_univ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:40:56.79533+00:00
-- url     : https://prove2.me/theorems/885075be-3274-4b0b-9de9-6b10af03303d
-- title:
--   Channel Capacity: channel Capacity eq of is Max On univ
-- statement:
--   The Channel Capacity construction uses the channel Capacity eq of is Max On univ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Capacity.lean#L37-L54
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Capacity.lean#L37-L54

module
public import Definitions.Def_LeanPool_ChannelCapacity_NonDegeneracy
public import Definitions.Def_LeanPool_ChannelCapacity_StrictConcavity
public import Definitions.Def_LeanPool_ChannelCapacity_Capacity
set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory
open ProbabilityTheory
open ChannelCapacity
open ProbabilityMeasure
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

theorem ChannelCapacity.channelCapacity_eq_of_isMaxOn_univ (k : Kernel α β) [IsMarkovKernel k]
    {p : ProbabilityMeasure α}
    (hp : IsMaxOn (fun q => mutualInformation q k) Set.univ p) :
    channelCapacity k = mutualInformation p k := by sorry
