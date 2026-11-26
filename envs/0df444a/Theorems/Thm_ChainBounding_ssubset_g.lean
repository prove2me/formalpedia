-- Prove2me | Theorems.Thm_ChainBounding_ssubset_g
-- name    : ChainBounding.ssubset_g
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:45:50.777855+00:00
-- url     : https://prove2.me/theorems/9e7e56b1-9e99-5869-bd6f-9601a4f4043a
-- title:
--   Chain Bounding: ssubset g
-- statement:
--   The Chain Bounding construction uses the ssubset g property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sterraf/chain-bounding/blob/f3eb6e0becc13d645f0809c98ed28912ee41ee6a/Solution.lean#L402-L405
-- source:
--   https://github.com/sterraf/chain-bounding/blob/f3eb6e0becc13d645f0809c98ed28912ee41ee6a/Solution.lean#L402-L405

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

theorem ChainBounding.ssubset_g {C : Set α} (hC : IsChain (· ≤ ·) C) : C ⊂ g C := by sorry
