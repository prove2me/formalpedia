-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_growth_derivativeOrder
-- name    : BKAR.Forest.ActiveTerminalBranchData.growth_derivativeOrder
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:24:52.208644+00:00
-- url     : https://prove2.me/theorems/5a457a5b-aa22-5deb-9f2b-33257be0dc4a
-- title:
--   Active Terminal Branch Data: growth derivative Order
-- statement:
--   The Active Terminal Branch Data construction uses the growth derivative Order property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean#L425-L429
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean#L425-L429

import Definitions.Def_BKAR_OrderedRemainder
import Definitions.Def_BKAR_OrderedTerminalGrowth
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse
import Theorems.Thm_BKAR_Forest_ActiveBranchData_growth_derivativeOrder
import Theorems.Thm_BKAR_OrderedSimplexParams_tail

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveTerminalBranchData
variable {F : Forest V}

theorem BKAR.Forest.ActiveTerminalBranchData.growth_derivativeOrder (data : ActiveTerminalBranchData F)
    (e : {e // e ∈ F.activeEdges}) :
    ((data.growth e).growth).derivativeOrder =
      (e.val :: (data.tail e).order).reverse := by sorry
