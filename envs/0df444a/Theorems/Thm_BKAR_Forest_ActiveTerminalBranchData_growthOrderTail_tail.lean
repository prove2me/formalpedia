-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_growthOrderTail_tail
-- name    : BKAR.Forest.ActiveTerminalBranchData.growthOrderTail_tail
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:28:43.863676+00:00
-- url     : https://prove2.me/theorems/5fec53f2-a537-48a8-9fad-0d1688724d9f
-- title:
--   Active Terminal Branch Data: growth Order Tail tail
-- statement:
--   The Active Terminal Branch Data construction uses the growth Order Tail tail property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Support/Growth.lean#L136-L140
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Support/Growth.lean#L136-L140

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

theorem BKAR.Forest.ActiveTerminalBranchData.growthOrderTail_tail
    (data : ActiveTerminalBranchData (Forest.empty V))
    (e : {e // e ∈ (Forest.empty V).activeEdges}) :
    (data.growthOrderTail e).2 = (data.tail e).order := by sorry
