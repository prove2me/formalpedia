-- Prove2me | Theorems.Thm_BKAR_Forest_TerminalGrowth_order_mem_edgeOrders_of_initial_edges_eq_empty
-- name    : BKAR.Forest.TerminalGrowth.order_mem_edgeOrders_of_initial_edges_eq_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:46:46.078695+00:00
-- url     : https://prove2.me/theorems/e86129b4-3980-43cb-8aa9-406f205b1c5b
-- title:
--   Terminal Growth: order mem edge Orders of initial edges eq empty
-- statement:
--   A terminal branch grown from an initially empty edge set carries one of the
--   canonical edge orderings of its terminal forest.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Branches.lean#L70-L75
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Branches.lean#L70-L75

import Definitions.Def_BKAR_CubePartition_Orders
import Definitions.Def_BKAR_CubePartition_Branches
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.TerminalGrowth
variable {F : Forest V}

theorem BKAR.Forest.TerminalGrowth.order_mem_edgeOrders_of_initial_edges_eq_empty
    (data : TerminalGrowth F) (hF : F.edges = ∅) :
    data.order ∈ data.terminal.edgeOrders := by sorry
