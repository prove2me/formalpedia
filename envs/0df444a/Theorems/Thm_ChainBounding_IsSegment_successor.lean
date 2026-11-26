-- Prove2me | Theorems.Thm_ChainBounding_IsSegment_successor
-- name    : ChainBounding.IsSegment_successor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:45:53.862811+00:00
-- url     : https://prove2.me/theorems/55cf58ee-c1d8-44c0-9c95-b735b9a14627
-- title:
--   Chain Bounding: Is Segment successor
-- statement:
--   A chain is a segment of its successor.
--
--   Source: https://github.com/sterraf/chain-bounding/blob/f3eb6e0becc13d645f0809c98ed28912ee41ee6a/Solution.lean#L449-L456
-- source:
--   https://github.com/sterraf/chain-bounding/blob/f3eb6e0becc13d645f0809c98ed28912ee41ee6a/Solution.lean#L449-L456

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

theorem ChainBounding.IsSegment_successor {C : Set α} (chain : IsChain (· ≤ ·) C) : IsSegment C (g C) := by sorry
