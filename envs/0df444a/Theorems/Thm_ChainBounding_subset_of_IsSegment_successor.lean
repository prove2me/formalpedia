-- Prove2me | Theorems.Thm_ChainBounding_subset_of_IsSegment_successor
-- name    : ChainBounding.subset_of_IsSegment_successor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:45:53.545412+00:00
-- url     : https://prove2.me/theorems/c598564c-6285-4f35-9bab-0a7f877efc75
-- title:
--   Chain Bounding: subset of Is Segment successor
-- statement:
--   The Chain Bounding construction uses the subset of Is Segment successor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sterraf/chain-bounding/blob/f3eb6e0becc13d645f0809c98ed28912ee41ee6a/Solution.lean#L438-L444
-- source:
--   https://github.com/sterraf/chain-bounding/blob/f3eb6e0becc13d645f0809c98ed28912ee41ee6a/Solution.lean#L438-L444

import Mathlib.Order.Preorder.Chain
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.WellFoundedSet
import Definitions.Def_ChainBounding_Solution
set_option autoImplicit true
variable {α : Type*}
open Set IsChain
noncomputable section
variable [PartialOrder α] [OrderSelector α] [ChainBounding α]
open OrderSelector OrderExpander
open ChainBounding

theorem ChainBounding.subset_of_IsSegment_successor {C S : Set α} [Chain C] (Sprseg : S ⊏ (g C)) : S ⊆ C := by sorry
