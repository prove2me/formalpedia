-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_growth_support_eq_singleton_iff_emptyStart
-- name    : BKAR.Forest.ActiveTerminalBranchData.growth_support_eq_singleton_iff_emptyStart
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:54:37.994931+00:00
-- url     : https://prove2.me/theorems/6ab85fd2-1457-5d6f-a35e-13328c96f6b7
-- title:
--   Active Terminal Branch Data: growth support eq singleton iff empty Start
-- statement:
--   A selected terminal branch from the empty forest has singleton support exactly
--   when its first edge is that singleton and its tail order is empty.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Support/Terminal.lean#L190-L211
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Support/Terminal.lean#L190-L211

import Definitions.Def_BKAR_CubePartition_Support_Contribution
import Definitions.Def_BKAR_CubePartition_Support_Terminal
import Theorems.Thm_BKAR_OrderedSimplexParams_tail

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveTerminalBranchData
variable {F : Forest V}

theorem BKAR.Forest.ActiveTerminalBranchData.growth_support_eq_singleton_iff_emptyStart
    (data : ActiveTerminalBranchData (Forest.empty V))
    (e : {e // e ∈ (Forest.empty V).activeEdges})
    (a : Edge V) :
    (data.growth e).support = ForestIndex.singleton a ↔
      e.val = a ∧ (data.tail e).order = [] := by sorry
