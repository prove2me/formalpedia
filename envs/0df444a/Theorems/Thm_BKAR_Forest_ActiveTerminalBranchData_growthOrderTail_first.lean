-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_growthOrderTail_first
-- name    : BKAR.Forest.ActiveTerminalBranchData.growthOrderTail_first
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:28:38.82895+00:00
-- url     : https://prove2.me/theorems/5d6ffbbc-c42e-5d95-bd06-fc2f3560afca
-- title:
--   Active Terminal Branch Data: growth Order Tail first
-- statement:
--   The Active Terminal Branch Data construction uses the growth Order Tail first property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Support/Growth.lean#L130-L134
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Support/Growth.lean#L130-L134

import Definitions.Def_BKAR_CubePartition_Branches
import Definitions.Def_BKAR_CubePartition_Support_Growth
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveTerminalBranchData
variable {F : Forest V}

theorem BKAR.Forest.ActiveTerminalBranchData.growthOrderTail_first
    (data : ActiveTerminalBranchData (Forest.empty V))
    (e : {e // e ∈ (Forest.empty V).activeEdges}) :
    (data.growthOrderTail e).1.val = e.val := by sorry
