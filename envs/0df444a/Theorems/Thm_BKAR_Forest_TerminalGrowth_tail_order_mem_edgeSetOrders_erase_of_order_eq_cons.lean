-- Prove2me | Theorems.Thm_BKAR_Forest_TerminalGrowth_tail_order_mem_edgeSetOrders_erase_of_order_eq_cons
-- name    : BKAR.Forest.TerminalGrowth.tail_order_mem_edgeSetOrders_erase_of_order_eq_cons
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:27:23.983484+00:00
-- url     : https://prove2.me/theorems/1b4d49ee-8cac-576a-b673-96aa166bc302
-- title:
--   Terminal Growth: tail order mem edge Set Orders erase of order eq cons
-- statement:
--   If an empty-start terminal branch order is nonempty, its tail is one of the
--   canonical orders of the terminal edge set with the first edge erased.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Branches.lean#L86-L94
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Branches.lean#L86-L94

import Definitions.Def_BKAR_CubePartition_Orders
import Definitions.Def_BKAR_CubePartition_Branches
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.TerminalGrowth
variable {F : Forest V}

theorem BKAR.Forest.TerminalGrowth.tail_order_mem_edgeSetOrders_erase_of_order_eq_cons
    (data : TerminalGrowth (Forest.empty V))
    {e : Edge V} {order : List (Edge V)}
    (horder : data.order = e :: order) :
    order ∈ edgeSetOrders (data.terminal.edges.erase e) := by sorry
