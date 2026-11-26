-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveBranchData_growth_firstStep
-- name    : BKAR.Forest.ActiveBranchData.growth_firstStep
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:21:04.742268+00:00
-- url     : https://prove2.me/theorems/77628b59-3d52-4db8-9b8d-8d9c371f3a66
-- title:
--   Active Branch Data: growth first Step
-- statement:
--   The Active Branch Data construction uses the growth first Step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedRemainder.lean#L73-L76
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedRemainder.lean#L73-L76

import Definitions.Def_BKAR_OrderedRecursion
import Definitions.Def_BKAR_OrderedRemainder
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveBranchData
variable {F : Forest V}

theorem BKAR.Forest.ActiveBranchData.growth_firstStep (data : ActiveBranchData F)
    (e : {e // e ∈ F.activeEdges}) :
    (data.growth e).firstStep = (data.extension e).extension := by sorry
