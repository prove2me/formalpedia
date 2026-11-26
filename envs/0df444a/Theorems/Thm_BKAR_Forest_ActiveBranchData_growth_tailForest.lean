-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveBranchData_growth_tailForest
-- name    : BKAR.Forest.ActiveBranchData.growth_tailForest
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:21:11.049861+00:00
-- url     : https://prove2.me/theorems/102ee379-af13-52ce-b643-35a446bf54ef
-- title:
--   Active Branch Data: growth tail Forest
-- statement:
--   The Active Branch Data construction uses the growth tail Forest property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedRemainder.lean#L78-L81
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedRemainder.lean#L78-L81

import Definitions.Def_BKAR_OrderedRecursion
import Definitions.Def_BKAR_OrderedRemainder
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveBranchData
variable {F : Forest V}

theorem BKAR.Forest.ActiveBranchData.growth_tailForest (data : ActiveBranchData F)
    (e : {e // e ∈ F.activeEdges}) :
    (data.growth e).tailForest = (data.extension e).forest := by sorry
