-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_growth_support_edges_eq_toFinset_emptyStart
-- name    : BKAR.Forest.ActiveTerminalBranchData.growth_support_edges_eq_toFinset_emptyStart
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:54:23.366318+00:00
-- url     : https://prove2.me/theorems/885ccc9c-eca8-4132-b5b2-c32cabed3c64
-- title:
--   Active Terminal Branch Data: growth support edges eq to Finset empty Start
-- statement:
--   The support index of an active-terminal branch from the empty forest carries
--   the same edge set as its selected first-edge/tail order.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Support/Growth.lean#L57-L62
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Support/Growth.lean#L57-L62

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

theorem BKAR.Forest.ActiveTerminalBranchData.growth_support_edges_eq_toFinset_emptyStart
    (data : ActiveTerminalBranchData (Forest.empty V))
    (e : {e // e ∈ (Forest.empty V).activeEdges}) :
    (data.growth e).support.edges =
      (e.val :: (data.tail e).order).toFinset := by sorry
