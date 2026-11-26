-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_growth_order_mem_edgeSetOrders_of_support_eq_emptyStart
-- name    : BKAR.Forest.ActiveTerminalBranchData.growth_order_mem_edgeSetOrders_of_support_eq_emptyStart
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:54:24.749487+00:00
-- url     : https://prove2.me/theorems/6aa10a38-76e0-5873-be0d-e1ab941f3a3d
-- title:
--   Active Terminal Branch Data: growth order mem edge Set Orders of support eq empty Start
-- statement:
--   A selected terminal branch lying over support `I` carries a canonical ordering
--   of the edge set `I.edges`.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Support/Contribution.lean#L352-L361
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Support/Contribution.lean#L352-L361

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

theorem BKAR.Forest.ActiveTerminalBranchData.growth_order_mem_edgeSetOrders_of_support_eq_emptyStart
    (data : ActiveTerminalBranchData (Forest.empty V))
    (e : {e // e ∈ (Forest.empty V).activeEdges})
    {I : ForestIndex V} (hsupport : (data.growth e).support = I) :
    (e.val :: (data.tail e).order) ∈ edgeSetOrders I.edges := by sorry
