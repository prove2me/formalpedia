-- Prove2me | Theorems.Thm_ChannelCapacity_exists_capacity_achieving_prior
-- name    : ChannelCapacity.exists_capacity_achieving_prior
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:40:56.806076+00:00
-- url     : https://prove2.me/theorems/d0a6d32b-8dc3-4d71-8dae-e335a6448b3f
-- title:
--   Channel Capacity: exists capacity achieving prior
-- statement:
--   The Channel Capacity construction uses the exists capacity achieving prior property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Capacity.lean#L69-L76
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Capacity.lean#L69-L76

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

theorem ChannelCapacity.exists_capacity_achieving_prior (k : Kernel α β) [IsMarkovKernel k]
    [TopologicalSpace (ProbabilityMeasure α)]
    (hNonempty : (Set.univ : Set (ProbabilityMeasure α)).Nonempty)
    (hCompact : IsCompact (Set.univ : Set (ProbabilityMeasure α)))
    (hUsc : UpperSemicontinuous fun p : ProbabilityMeasure α => mutualInformation p k) :
    ∃ p : ProbabilityMeasure α, IsCapacityAchievingPrior k p := by sorry
