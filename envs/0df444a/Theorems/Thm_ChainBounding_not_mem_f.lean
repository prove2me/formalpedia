-- Prove2me | Theorems.Thm_ChainBounding_not_mem_f
-- name    : ChainBounding.not_mem_f
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:45:52.002897+00:00
-- url     : https://prove2.me/theorems/1c79128b-e71c-498c-9600-3843286f7fd3
-- title:
--   Chain Bounding: not mem f
-- statement:
--   The Chain Bounding construction uses the not mem f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sterraf/chain-bounding/blob/f3eb6e0becc13d645f0809c98ed28912ee41ee6a/Solution.lean#L398-L400
-- source:
--   https://github.com/sterraf/chain-bounding/blob/f3eb6e0becc13d645f0809c98ed28912ee41ee6a/Solution.lean#L398-L400

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

theorem ChainBounding.not_mem_f {C : Set α} (hC : IsChain (· ≤ ·) C) : f C ∉ C := by sorry
