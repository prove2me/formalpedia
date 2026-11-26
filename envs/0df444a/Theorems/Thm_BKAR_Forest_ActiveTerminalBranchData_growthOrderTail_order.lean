-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_growthOrderTail_order
-- name    : BKAR.Forest.ActiveTerminalBranchData.growthOrderTail_order
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:55:49.540306+00:00
-- url     : https://prove2.me/theorems/115787f3-9bce-4ec1-a642-2c54b38fcae1
-- title:
--   Active Terminal Branch Data: growth Order Tail order
-- statement:
--   The Active Terminal Branch Data construction uses the growth Order Tail order property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Support/Growth.lean#L142-L147
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Support/Growth.lean#L142-L147

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

theorem BKAR.Forest.ActiveTerminalBranchData.growthOrderTail_order
    (data : ActiveTerminalBranchData (Forest.empty V))
    (e : {e // e ∈ (Forest.empty V).activeEdges}) :
    (data.growthOrderTail e).1.val :: (data.growthOrderTail e).2 =
      e.val :: (data.tail e).order := by sorry
