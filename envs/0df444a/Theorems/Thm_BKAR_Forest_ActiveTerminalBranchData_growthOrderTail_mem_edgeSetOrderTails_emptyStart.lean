-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_growthOrderTail_mem_edgeSetOrderTails_emptyStart
-- name    : BKAR.Forest.ActiveTerminalBranchData.growthOrderTail_mem_edgeSetOrderTails_emptyStart
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:28:59.721163+00:00
-- url     : https://prove2.me/theorems/461d25b4-82ca-58b1-954e-82f30744ccec
-- title:
--   Active Terminal Branch Data: growth Order Tail mem edge Set Order Tails empty Start
-- statement:
--   The Active Terminal Branch Data construction uses the growth Order Tail mem edge Set Order Tails empty Start property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Support/Growth.lean#L161-L168
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Support/Growth.lean#L161-L168

import Definitions.Def_BKAR_CubePartition_Branches
import Definitions.Def_BKAR_CubePartition_Support_Growth
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveTerminalBranchData
variable {F : Forest V}

theorem BKAR.Forest.ActiveTerminalBranchData.growthOrderTail_mem_edgeSetOrderTails_emptyStart
    (data : ActiveTerminalBranchData (Forest.empty V))
    (e : {e // e ∈ (Forest.empty V).activeEdges}) :
    data.growthOrderTail e ∈
      edgeSetOrderTails (data.growth e).terminal.edges := by sorry
