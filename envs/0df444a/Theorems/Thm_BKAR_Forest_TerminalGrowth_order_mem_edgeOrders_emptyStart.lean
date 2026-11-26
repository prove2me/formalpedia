-- Prove2me | Theorems.Thm_BKAR_Forest_TerminalGrowth_order_mem_edgeOrders_emptyStart
-- name    : BKAR.Forest.TerminalGrowth.order_mem_edgeOrders_emptyStart
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:46:01.618286+00:00
-- url     : https://prove2.me/theorems/4daedc67-5445-4367-a009-2b8aed210d75
-- title:
--   Terminal Growth: order mem edge Orders empty Start
-- statement:
--   The Terminal Growth construction uses the order mem edge Orders empty Start property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Branches.lean#L77-L80
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Branches.lean#L77-L80

import Definitions.Def_BKAR_CubePartition_Orders
import Definitions.Def_BKAR_CubePartition_Branches
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.TerminalGrowth
variable {F : Forest V}

theorem BKAR.Forest.TerminalGrowth.order_mem_edgeOrders_emptyStart
    (data : TerminalGrowth (Forest.empty V)) :
    data.order ∈ data.terminal.edgeOrders := by sorry
