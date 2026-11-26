-- Prove2me | Theorems.Thm_BKAR_Forest_OrderedGrowth_tail_order_mem_edgeSetOrders_erase_emptyStart
-- name    : BKAR.Forest.OrderedGrowth.tail_order_mem_edgeSetOrders_erase_emptyStart
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:27:11.884076+00:00
-- url     : https://prove2.me/theorems/2c9012a3-72ef-4ba8-a8cd-eee5444d55f4
-- title:
--   Ordered Growth: tail order mem edge Set Orders erase empty Start
-- statement:
--   The Ordered Growth construction uses the tail order mem edge Set Orders erase empty Start property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Branches.lean#L54-L58
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Branches.lean#L54-L58

import Definitions.Def_BKAR_CubePartition_Orders
import Definitions.Def_BKAR_CubePartition_Branches
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {F G : Forest V} {order : List (Edge V)}

theorem BKAR.Forest.OrderedGrowth.tail_order_mem_edgeSetOrders_erase_emptyStart
    {e : Edge V} (h : OrderedGrowth (Forest.empty V) (e :: order) G) :
    order ∈ edgeSetOrders (G.edges.erase e) := by sorry
