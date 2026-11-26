-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_growth_growth
-- name    : BKAR.Forest.ActiveTerminalBranchData.growth_growth
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:24:42.066234+00:00
-- url     : https://prove2.me/theorems/bf801026-6d0a-4a76-935a-cfb1e3a19f93
-- title:
--   Active Terminal Branch Data: growth growth
-- statement:
--   The Active Terminal Branch Data construction uses the growth growth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean#L419-L423
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean#L419-L423

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

theorem BKAR.Forest.ActiveTerminalBranchData.growth_growth (data : ActiveTerminalBranchData F)
    (e : {e // e ∈ F.activeEdges}) :
    (data.growth e).growth =
      (data.extension e).consGrowth (data.tail e).growth := by sorry
