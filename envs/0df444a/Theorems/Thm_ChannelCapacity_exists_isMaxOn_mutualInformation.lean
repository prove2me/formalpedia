-- Prove2me | Theorems.Thm_ChannelCapacity_exists_isMaxOn_mutualInformation
-- name    : ChannelCapacity.exists_isMaxOn_mutualInformation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:41:05.244109+00:00
-- url     : https://prove2.me/theorems/e5d1cc7d-8734-4e30-8660-48b323b19105
-- title:
--   Channel Capacity: exists is Max On mutual Information
-- statement:
--   The Channel Capacity construction uses the exists is Max On mutual Information property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Capacity.lean#L56-L67
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Capacity.lean#L56-L67

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

theorem ChannelCapacity.exists_isMaxOn_mutualInformation (k : Kernel α β) [IsMarkovKernel k]
    [TopologicalSpace (ProbabilityMeasure α)]
    (hNonempty : (Set.univ : Set (ProbabilityMeasure α)).Nonempty)
    (hCompact : IsCompact (Set.univ : Set (ProbabilityMeasure α)))
    (hUsc : UpperSemicontinuous fun p : ProbabilityMeasure α => mutualInformation p k) :
    ∃ p : ProbabilityMeasure α,
      IsMaxOn (fun q => mutualInformation q k) Set.univ p := by sorry
