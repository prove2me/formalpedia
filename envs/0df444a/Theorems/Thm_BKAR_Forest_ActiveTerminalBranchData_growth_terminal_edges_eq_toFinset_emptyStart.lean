-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_growth_terminal_edges_eq_toFinset_emptyStart
-- name    : BKAR.Forest.ActiveTerminalBranchData.growth_terminal_edges_eq_toFinset_emptyStart
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:53:59.797346+00:00
-- url     : https://prove2.me/theorems/b3b2bc80-5848-45bb-94ca-6bb6305a9e60
-- title:
--   Active Terminal Branch Data: growth terminal edges eq to Finset empty Start
-- statement:
--   For an active-terminal branch from the empty forest, the terminal edge set is
--   exactly the edge set represented by the selected first edge and tail order.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Support/Growth.lean#L46-L51
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Support/Growth.lean#L46-L51

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

theorem BKAR.Forest.ActiveTerminalBranchData.growth_terminal_edges_eq_toFinset_emptyStart
    (data : ActiveTerminalBranchData (Forest.empty V))
    (e : {e // e ∈ (Forest.empty V).activeEdges}) :
    (data.growth e).terminal.edges =
      (e.val :: (data.tail e).order).toFinset := by sorry
