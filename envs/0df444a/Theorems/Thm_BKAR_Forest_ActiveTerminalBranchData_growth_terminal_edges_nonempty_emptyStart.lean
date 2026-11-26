-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_growth_terminal_edges_nonempty_emptyStart
-- name    : BKAR.Forest.ActiveTerminalBranchData.growth_terminal_edges_nonempty_emptyStart
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:55:29.656459+00:00
-- url     : https://prove2.me/theorems/6864b481-5784-41af-9b75-92b2eb2fb1f7
-- title:
--   Active Terminal Branch Data: growth terminal edges nonempty empty Start
-- statement:
--   Every active-terminal branch selected from the empty forest has a nonempty
--   terminal edge set: it contains the first active edge of the branch.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Support/Growth.lean#L75-L82
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Support/Growth.lean#L75-L82

import Definitions.Def_BKAR_CubePartition_Branches
import Definitions.Def_BKAR_CubePartition_Support_Growth
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveTerminalBranchData
variable {F : Forest V}

theorem BKAR.Forest.ActiveTerminalBranchData.growth_terminal_edges_nonempty_emptyStart
    (data : ActiveTerminalBranchData (Forest.empty V))
    (e : {e // e ∈ (Forest.empty V).activeEdges}) :
    (data.growth e).terminal.edges.Nonempty := by sorry
