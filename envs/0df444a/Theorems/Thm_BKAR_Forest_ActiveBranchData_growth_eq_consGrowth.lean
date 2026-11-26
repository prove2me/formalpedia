-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveBranchData_growth_eq_consGrowth
-- name    : BKAR.Forest.ActiveBranchData.growth_eq_consGrowth
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:20:59.190479+00:00
-- url     : https://prove2.me/theorems/9877ab14-00c2-5a57-a5d7-23c171ca8507
-- title:
--   Active Branch Data: growth eq cons Growth
-- statement:
--   The Active Branch Data construction uses the growth eq cons Growth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedRemainder.lean#L68-L71
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedRemainder.lean#L68-L71

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

theorem BKAR.Forest.ActiveBranchData.growth_eq_consGrowth (data : ActiveBranchData F)
    (e : {e // e ∈ F.activeEdges}) :
    data.growth e = (data.extension e).consGrowth (data.tail e) := by sorry
