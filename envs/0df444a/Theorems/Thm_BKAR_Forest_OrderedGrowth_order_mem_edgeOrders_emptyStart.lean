-- Prove2me | Theorems.Thm_BKAR_Forest_OrderedGrowth_order_mem_edgeOrders_emptyStart
-- name    : BKAR.Forest.OrderedGrowth.order_mem_edgeOrders_emptyStart
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:46:09.109631+00:00
-- url     : https://prove2.me/theorems/4b68ba7e-c698-46f2-8d77-1d16489b0730
-- title:
--   Ordered Growth: order mem edge Orders empty Start
-- statement:
--   The Ordered Growth construction uses the order mem edge Orders empty Start property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Branches.lean#L38-L41
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Branches.lean#L38-L41

import Definitions.Def_BKAR_CubePartition_Orders
import Definitions.Def_BKAR_CubePartition_Branches
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {F G : Forest V} {order : List (Edge V)}

theorem BKAR.Forest.OrderedGrowth.order_mem_edgeOrders_emptyStart
    (h : OrderedGrowth (Forest.empty V) order G) :
    order ∈ G.edgeOrders := by sorry
