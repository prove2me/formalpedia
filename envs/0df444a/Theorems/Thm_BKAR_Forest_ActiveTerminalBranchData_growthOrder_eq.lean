-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_growthOrder_eq
-- name    : BKAR.Forest.ActiveTerminalBranchData.growthOrder_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:52:59.046183+00:00
-- url     : https://prove2.me/theorems/0f7d95fa-8c72-521a-8b99-b4093e14c001
-- title:
--   Active Terminal Branch Data: growth Order eq
-- statement:
--   The Active Terminal Branch Data construction uses the growth Order eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Support/Growth.lean#L155-L159
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Support/Growth.lean#L155-L159

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

theorem BKAR.Forest.ActiveTerminalBranchData.growthOrder_eq
    (data : ActiveTerminalBranchData (Forest.empty V))
    (e : {e // e ∈ (Forest.empty V).activeEdges}) :
    data.growthOrder e = e.val :: (data.tail e).order := by sorry
