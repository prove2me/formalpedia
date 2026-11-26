-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_branchData_growth
-- name    : BKAR.Forest.ActiveTerminalBranchData.branchData_growth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:24:32.741989+00:00
-- url     : https://prove2.me/theorems/b1da8736-91a1-4875-9fa0-f344b21160b4
-- title:
--   Active Terminal Branch Data: branch Data growth
-- statement:
--   The Active Terminal Branch Data construction uses the branch Data growth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean#L380-L383
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean#L380-L383

import Definitions.Def_BKAR_OrderedRemainder
import Definitions.Def_BKAR_OrderedTerminalGrowth
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveTerminalBranchData
variable {F : Forest V}

theorem BKAR.Forest.ActiveTerminalBranchData.branchData_growth (data : ActiveTerminalBranchData F)
    (e : {e // e ∈ F.activeEdges}) :
    data.branchData.growth e = (data.growth e).growth := by sorry
