-- Prove2me | Theorems.Thm_BKAR_Forest_OrderedGrowth_order_mem_edgeOrders_of_initial_edges_eq_empty
-- name    : BKAR.Forest.OrderedGrowth.order_mem_edgeOrders_of_initial_edges_eq_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:45:49.977532+00:00
-- url     : https://prove2.me/theorems/7315b4c1-9d2d-5ec9-86b0-6e4d208153ee
-- title:
--   Ordered Growth: order mem edge Orders of initial edges eq empty
-- statement:
--   An ordered growth from an initially empty edge set carries one of the canonical
--   edge orderings of its terminal forest.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Branches.lean#L29-L36
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Branches.lean#L29-L36

import Definitions.Def_BKAR_CubePartition_Orders
import Definitions.Def_BKAR_CubePartition_Branches
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {F G : Forest V} {order : List (Edge V)}

theorem BKAR.Forest.OrderedGrowth.order_mem_edgeOrders_of_initial_edges_eq_empty
    (h : OrderedGrowth F order G) (hF : F.edges = ∅) :
    order ∈ G.edgeOrders := by sorry
