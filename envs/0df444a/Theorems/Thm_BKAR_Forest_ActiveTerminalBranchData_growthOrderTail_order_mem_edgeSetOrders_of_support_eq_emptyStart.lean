-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_growthOrderTail_order_mem_edgeSetOrders_of_support_eq_emptyStart
-- name    : BKAR.Forest.ActiveTerminalBranchData.growthOrderTail_order_mem_edgeSetOrders_of_support_eq_emptyStart
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:01:39.152003+00:00
-- url     : https://prove2.me/theorems/0d3218d4-6da4-42b4-a93f-81fb664ddfe6
-- title:
--   Active Terminal Branch Data: growth Order Tail order mem edge Set Orders of support eq empty Start
-- statement:
--   The packaged first-edge/tail sector of a selected terminal branch over `I` is
--   one of the canonical orderings of `I.edges`.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Support/Contribution.lean#L380-L388
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Support/Contribution.lean#L380-L388

import Definitions.Def_BKAR_CubePartition_Support_Growth
import Definitions.Def_BKAR_CubePartition_Support_Contribution
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveTerminalBranchData
variable {F : Forest V}

theorem BKAR.Forest.ActiveTerminalBranchData.growthOrderTail_order_mem_edgeSetOrders_of_support_eq_emptyStart
    (data : ActiveTerminalBranchData (Forest.empty V))
    (e : {e // e ∈ (Forest.empty V).activeEdges})
    {I : ForestIndex V} (hsupport : (data.growth e).support = I) :
    ((data.growthOrderTail e).1.val :: (data.growthOrderTail e).2) ∈
      edgeSetOrders I.edges := by sorry
