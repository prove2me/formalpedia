-- Prove2me | Theorems.Thm_ChainBounding_Good_successor
-- name    : ChainBounding.Good_successor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:45:53.101317+00:00
-- url     : https://prove2.me/theorems/9b468da6-a97e-5a2d-a4e0-6f6387975fdf
-- title:
--   Chain Bounding: Good successor
-- statement:
--   The successor good chain is good as well.
--
--   Source: https://github.com/sterraf/chain-bounding/blob/f3eb6e0becc13d645f0809c98ed28912ee41ee6a/Solution.lean#L461-L476
-- source:
--   https://github.com/sterraf/chain-bounding/blob/f3eb6e0becc13d645f0809c98ed28912ee41ee6a/Solution.lean#L461-L476

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

theorem ChainBounding.Good_successor (C : Set α) (goodC : Good C) : Good (g C) := by sorry
