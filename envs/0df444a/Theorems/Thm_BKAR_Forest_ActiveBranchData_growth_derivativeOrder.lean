-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveBranchData_growth_derivativeOrder
-- name    : BKAR.Forest.ActiveBranchData.growth_derivativeOrder
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:41:44.327801+00:00
-- url     : https://prove2.me/theorems/29809963-4f8b-4e5d-8769-a1efb3d16220
-- title:
--   Active Branch Data: growth derivative Order
-- statement:
--   The Active Branch Data construction uses the growth derivative Order property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedRemainder.lean#L93-L96
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedRemainder.lean#L93-L96

import Definitions.Def_BKAR_OrderedRecursion
import Definitions.Def_BKAR_OrderedRemainder
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveBranchData
variable {F : Forest V}

theorem BKAR.Forest.ActiveBranchData.growth_derivativeOrder (data : ActiveBranchData F)
    (e : {e // e ∈ F.activeEdges}) :
    (data.growth e).derivativeOrder = (data.order e).reverse ++ [e.val] := by sorry
