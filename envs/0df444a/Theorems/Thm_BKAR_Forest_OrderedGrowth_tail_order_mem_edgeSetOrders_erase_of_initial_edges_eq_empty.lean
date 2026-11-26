-- Prove2me | Theorems.Thm_BKAR_Forest_OrderedGrowth_tail_order_mem_edgeSetOrders_erase_of_initial_edges_eq_empty
-- name    : BKAR.Forest.OrderedGrowth.tail_order_mem_edgeSetOrders_erase_of_initial_edges_eq_empty
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:48:46.362466+00:00
-- url     : https://prove2.me/theorems/b76469b4-c5e9-4be0-855b-df3fcc2a8873
-- title:
--   Ordered Growth: tail order mem edge Set Orders erase of initial edges eq empty
-- statement:
--   If an ordered growth starts from an empty edge set and has a first edge, then
--   the remaining growth order is a canonical ordering of the terminal edge set
--   with that first edge erased.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Branches.lean#L48-L52
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Branches.lean#L48-L52

import Definitions.Def_BKAR_CubePartition_Orders
import Definitions.Def_BKAR_CubePartition_Branches
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {F G : Forest V} {order : List (Edge V)}

theorem BKAR.Forest.OrderedGrowth.tail_order_mem_edgeSetOrders_erase_of_initial_edges_eq_empty
    {e : Edge V} (h : OrderedGrowth F (e :: order) G) (hF : F.edges = ∅) :
    order ∈ edgeSetOrders (G.edges.erase e) := by sorry
