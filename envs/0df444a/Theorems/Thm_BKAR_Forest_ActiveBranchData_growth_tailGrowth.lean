-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveBranchData_growth_tailGrowth
-- name    : BKAR.Forest.ActiveBranchData.growth_tailGrowth
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:21:15.536348+00:00
-- url     : https://prove2.me/theorems/97a6a00e-1304-41e7-88fd-5bc6625a99d6
-- title:
--   Active Branch Data: growth tail Growth
-- statement:
--   The Active Branch Data construction uses the growth tail Growth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedRemainder.lean#L83-L86
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedRemainder.lean#L83-L86

import Definitions.Def_BKAR_OrderedRecursion
import Definitions.Def_BKAR_OrderedRemainder
import Theorems.Thm_BKAR_OrderedSimplexParams_tail

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveBranchData
variable {F : Forest V}

theorem BKAR.Forest.ActiveBranchData.growth_tailGrowth (data : ActiveBranchData F)
    (e : {e // e ∈ F.activeEdges}) :
    (data.growth e).tailGrowth = data.tail e := by sorry
