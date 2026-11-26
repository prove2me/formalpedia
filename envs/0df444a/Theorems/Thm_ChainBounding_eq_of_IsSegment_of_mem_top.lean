-- Prove2me | Theorems.Thm_ChainBounding_eq_of_IsSegment_of_mem_top
-- name    : ChainBounding.eq_of_IsSegment_of_mem_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:45:50.356156+00:00
-- url     : https://prove2.me/theorems/27ab8038-9cc2-5836-8f87-0d9ded8a1e62
-- title:
--   Chain Bounding: eq of Is Segment of mem top
-- statement:
--   A segment containing the top element is the whole thing.
--
--   Source: https://github.com/sterraf/chain-bounding/blob/f3eb6e0becc13d645f0809c98ed28912ee41ee6a/Solution.lean#L431-L436
-- source:
--   https://github.com/sterraf/chain-bounding/blob/f3eb6e0becc13d645f0809c98ed28912ee41ee6a/Solution.lean#L431-L436

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
omit [OrderSelector α] [ChainBounding α]

theorem ChainBounding.eq_of_IsSegment_of_mem_top {C S : Set α} [OrderTop ↑C] (Sseg : IsSegment S C)
    (topin : ((⊤ : C) : α) ∈ S) : S = C := by sorry
