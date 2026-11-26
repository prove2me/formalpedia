-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_growth_order
-- name    : BKAR.Forest.ActiveTerminalBranchData.growth_order
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:24:28.344844+00:00
-- url     : https://prove2.me/theorems/ca544282-338e-556a-93cb-fe9b59a218e5
-- title:
--   Active Terminal Branch Data: growth order
-- statement:
--   The Active Terminal Branch Data construction uses the growth order property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean#L385-L388
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean#L385-L388

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

theorem BKAR.Forest.ActiveTerminalBranchData.growth_order (data : ActiveTerminalBranchData F)
    (e : {e // e ∈ F.activeEdges}) :
    (data.growth e).order = e.val :: (data.tail e).order := by sorry
