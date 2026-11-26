-- Prove2me | Theorems.Thm_ChainBounding_chain_bounding
-- name    : ChainBounding.chain_bounding
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:45:29.972805+00:00
-- url     : https://prove2.me/theorems/4615f7fe-38ec-4b8e-9835-d00102f89a9f
-- title:
--   Chain Bounding: chain bounding
-- statement:
--   There is no assigment of a strict upper bound to each chain in a poset.
--
--   Source: https://github.com/sterraf/chain-bounding/blob/f3eb6e0becc13d645f0809c98ed28912ee41ee6a/Solution.lean#L482-L487
-- source:
--   https://github.com/sterraf/chain-bounding/blob/f3eb6e0becc13d645f0809c98ed28912ee41ee6a/Solution.lean#L482-L487

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
include α

theorem ChainBounding.chain_bounding : False := by sorry
