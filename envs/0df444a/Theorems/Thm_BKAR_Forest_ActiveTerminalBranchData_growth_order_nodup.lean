-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_growth_order_nodup
-- name    : BKAR.Forest.ActiveTerminalBranchData.growth_order_nodup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:49:00.029898+00:00
-- url     : https://prove2.me/theorems/db4342d9-5a44-40a6-96a9-ae90fe4c6e25
-- title:
--   Active Terminal Branch Data: growth order nodup
-- statement:
--   The Active Terminal Branch Data construction uses the growth order nodup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean#L444-L447
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean#L444-L447

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

theorem BKAR.Forest.ActiveTerminalBranchData.growth_order_nodup (data : ActiveTerminalBranchData F)
    (e : {e // e ∈ F.activeEdges}) :
    (e.val :: (data.tail e).order).Nodup := by sorry
