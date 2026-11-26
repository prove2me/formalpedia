-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveBranchData_growth_firstActiveExtension
-- name    : BKAR.Forest.ActiveBranchData.growth_firstActiveExtension
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:21:21.335152+00:00
-- url     : https://prove2.me/theorems/a29d3f08-3854-4188-930b-2bc50057b318
-- title:
--   Active Branch Data: growth first Active Extension
-- statement:
--   The Active Branch Data construction uses the growth first Active Extension property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedRemainder.lean#L88-L91
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedRemainder.lean#L88-L91

import Definitions.Def_BKAR_OrderedRecursion
import Definitions.Def_BKAR_OrderedRemainder
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveBranchData
variable {F : Forest V}

theorem BKAR.Forest.ActiveBranchData.growth_firstActiveExtension (data : ActiveBranchData F)
    (e : {e // e ∈ F.activeEdges}) :
    (data.growth e).firstActiveExtension = data.extension e := by sorry
