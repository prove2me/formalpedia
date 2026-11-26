-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_growthOrder_mem_edgeSetOrders_of_support_eq_emptyStart
-- name    : BKAR.Forest.ActiveTerminalBranchData.growthOrder_mem_edgeSetOrders_of_support_eq_emptyStart
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:54:43.96932+00:00
-- url     : https://prove2.me/theorems/2ab2ba72-33fc-48c1-904a-9843fc668daf
-- title:
--   Active Terminal Branch Data: growth Order mem edge Set Orders of support eq empty Start
-- statement:
--   The selected terminal order of a branch over support `I` is one of the
--   canonical orderings of `I.edges`.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Support/Contribution.lean#L394-L400
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Support/Contribution.lean#L394-L400

import Definitions.Def_BKAR_CubePartition_Support_Growth
import Definitions.Def_BKAR_CubePartition_Support_Contribution
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveTerminalBranchData
variable {F : Forest V}

theorem BKAR.Forest.ActiveTerminalBranchData.growthOrder_mem_edgeSetOrders_of_support_eq_emptyStart
    (data : ActiveTerminalBranchData (Forest.empty V))
    (e : {e // e ∈ (Forest.empty V).activeEdges})
    {I : ForestIndex V} (hsupport : (data.growth e).support = I) :
    data.growthOrder e ∈ edgeSetOrders I.edges := by sorry
