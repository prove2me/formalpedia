-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_growth_terminal
-- name    : BKAR.Forest.ActiveTerminalBranchData.growth_terminal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:24:41.75663+00:00
-- url     : https://prove2.me/theorems/1010204b-1bc6-4ff9-9619-2c162660fb91
-- title:
--   Active Terminal Branch Data: growth terminal
-- statement:
--   The Active Terminal Branch Data construction uses the growth terminal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean#L390-L393
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean#L390-L393

import Definitions.Def_BKAR_OrderedRemainder
import Definitions.Def_BKAR_OrderedTerminalGrowth
import Theorems.Thm_BKAR_OrderedSimplexParams_tail

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveTerminalBranchData
variable {F : Forest V}

theorem BKAR.Forest.ActiveTerminalBranchData.growth_terminal (data : ActiveTerminalBranchData F)
    (e : {e // e ∈ F.activeEdges}) :
    (data.growth e).terminal = (data.tail e).terminal := by sorry
