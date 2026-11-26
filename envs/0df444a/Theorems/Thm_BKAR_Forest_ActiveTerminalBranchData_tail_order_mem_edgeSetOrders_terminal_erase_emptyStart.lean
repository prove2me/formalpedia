-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_tail_order_mem_edgeSetOrders_terminal_erase_emptyStart
-- name    : BKAR.Forest.ActiveTerminalBranchData.tail_order_mem_edgeSetOrders_terminal_erase_emptyStart
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:28:22.167351+00:00
-- url     : https://prove2.me/theorems/9128e0df-92c4-483c-b5e7-247e6acca5b4
-- title:
--   Active Terminal Branch Data: tail order mem edge Set Orders terminal erase empty Start
-- statement:
--   The tail order selected after the first active edge of an empty-start
--   active-terminal branch is a canonical ordering of the terminal edge set with
--   that first edge erased.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Support/Growth.lean#L89-L95
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Support/Growth.lean#L89-L95

import Definitions.Def_BKAR_CubePartition_Branches
import Definitions.Def_BKAR_CubePartition_Support_Growth
import Theorems.Thm_BKAR_OrderedSimplexParams_tail

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveTerminalBranchData
variable {F : Forest V}

theorem BKAR.Forest.ActiveTerminalBranchData.tail_order_mem_edgeSetOrders_terminal_erase_emptyStart
    (data : ActiveTerminalBranchData (Forest.empty V))
    (e : {e // e ∈ (Forest.empty V).activeEdges}) :
    (data.tail e).order ∈
      edgeSetOrders ((data.growth e).terminal.edges.erase e.val) := by sorry
