-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_growth_order_toFinset_eq_terminal_edges_emptyStart
-- name    : BKAR.Forest.ActiveTerminalBranchData.growth_order_toFinset_eq_terminal_edges_emptyStart
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:28:07.533338+00:00
-- url     : https://prove2.me/theorems/bb577f93-af0b-5939-8495-d479226cb53c
-- title:
--   Active Terminal Branch Data: growth order to Finset eq terminal edges empty Start
-- statement:
--   The Active Terminal Branch Data construction uses the growth order to Finset eq terminal edges empty Start property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Support/Growth.lean#L64-L69
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Support/Growth.lean#L64-L69

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

theorem BKAR.Forest.ActiveTerminalBranchData.growth_order_toFinset_eq_terminal_edges_emptyStart
    (data : ActiveTerminalBranchData (Forest.empty V))
    (e : {e // e ∈ (Forest.empty V).activeEdges}) :
    (e.val :: (data.tail e).order).toFinset =
      (data.growth e).terminal.edges := by sorry
