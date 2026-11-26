-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_growth_orderTail_mem_edgeSetOrderTails_emptyStart
-- name    : BKAR.Forest.ActiveTerminalBranchData.growth_orderTail_mem_edgeSetOrderTails_emptyStart
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:28:40.285226+00:00
-- url     : https://prove2.me/theorems/872fb985-0180-5b39-88e0-70caf420f67e
-- title:
--   Active Terminal Branch Data: growth order Tail mem edge Set Order Tails empty Start
-- statement:
--   Each selected active-terminal branch from the empty forest determines a member
--   of the terminal first-edge/tail-order indexing set.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Support/Growth.lean#L101-L114
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Support/Growth.lean#L101-L114

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

theorem BKAR.Forest.ActiveTerminalBranchData.growth_orderTail_mem_edgeSetOrderTails_emptyStart
    (data : ActiveTerminalBranchData (Forest.empty V))
    (e : {e // e ∈ (Forest.empty V).activeEdges}) :
    ∃ he : e.val ∈ (data.growth e).terminal.edges,
      (⟨⟨e.val, he⟩, (data.tail e).order⟩ :
        Σ _ : {x : Edge V // x ∈ (data.growth e).terminal.edges},
          List (Edge V)) ∈
        edgeSetOrderTails (data.growth e).terminal.edges := by sorry
