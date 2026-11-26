-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_growth_tail_order_mem_edgeSetOrders_support_erase_emptyStart
-- name    : BKAR.Forest.ActiveTerminalBranchData.growth_tail_order_mem_edgeSetOrders_support_erase_emptyStart
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:55:58.808498+00:00
-- url     : https://prove2.me/theorems/ca579883-0b8f-412c-8d19-ce7fd87fa6e5
-- title:
--   Active Terminal Branch Data: growth tail order mem edge Set Orders support erase empty Start
-- statement:
--   The tail of a selected terminal branch over support `I` is a canonical ordering
--   of `I.edges` with the first edge erased.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Support/Contribution.lean#L327-L333
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Support/Contribution.lean#L327-L333

import Definitions.Def_BKAR_CubePartition_Support_Growth
import Definitions.Def_BKAR_CubePartition_Support_Contribution
import Theorems.Thm_BKAR_OrderedSimplexParams_tail

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveTerminalBranchData
variable {F : Forest V}

theorem BKAR.Forest.ActiveTerminalBranchData.growth_tail_order_mem_edgeSetOrders_support_erase_emptyStart
    (data : ActiveTerminalBranchData (Forest.empty V))
    (e : {e // e ∈ (Forest.empty V).activeEdges})
    {I : ForestIndex V} (hsupport : (data.growth e).support = I) :
    (data.tail e).order ∈ edgeSetOrders (I.edges.erase e.val) := by sorry
