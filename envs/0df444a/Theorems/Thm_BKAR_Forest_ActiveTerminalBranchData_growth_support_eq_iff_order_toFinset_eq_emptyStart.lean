-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_growth_support_eq_iff_order_toFinset_eq_emptyStart
-- name    : BKAR.Forest.ActiveTerminalBranchData.growth_support_eq_iff_order_toFinset_eq_emptyStart
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:53:54.168833+00:00
-- url     : https://prove2.me/theorems/36b5b879-f429-4fe7-8f82-8c85976e9e86
-- title:
--   Active Terminal Branch Data: growth support eq iff order to Finset eq empty Start
-- statement:
--   For selected terminal branches from the empty forest, equality of finite
--   supports is exactly equality of the selected order's edge set.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Support/Contribution.lean#L115-L127
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Support/Contribution.lean#L115-L127

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

theorem BKAR.Forest.ActiveTerminalBranchData.growth_support_eq_iff_order_toFinset_eq_emptyStart
    (data : ActiveTerminalBranchData (Forest.empty V))
    (e : {e // e ∈ (Forest.empty V).activeEdges})
    (I : ForestIndex V) :
    (data.growth e).support = I ↔
      (e.val :: (data.tail e).order).toFinset = I.edges := by sorry
