-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_branchData_terminal_activeEdges_eq_empty
-- name    : BKAR.Forest.ActiveTerminalBranchData.branchData_terminal_activeEdges_eq_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:43:41.375664+00:00
-- url     : https://prove2.me/theorems/9223385d-53e0-5059-916d-7e5270ad5ba3
-- title:
--   Active Terminal Branch Data: branch Data terminal active Edges eq empty
-- statement:
--   The Active Terminal Branch Data construction uses the branch Data terminal active Edges eq empty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean#L365-L369
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean#L365-L369

import Definitions.Def_BKAR_OrderedRemainder
import Definitions.Def_BKAR_OrderedTerminalGrowth
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveTerminalBranchData
variable {F : Forest V}

theorem BKAR.Forest.ActiveTerminalBranchData.branchData_terminal_activeEdges_eq_empty
    (data : ActiveTerminalBranchData F)
    (e : {e // e ∈ F.activeEdges}) :
    (data.branchData.terminal e).activeEdges = ∅ := by sorry
