-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveBranchData_singleton_growth_eq_singletonGrowth
-- name    : BKAR.Forest.ActiveBranchData.singleton_growth_eq_singletonGrowth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:21:36.529722+00:00
-- url     : https://prove2.me/theorems/b99014c7-b941-4ac1-8203-a8632b8cd4bc
-- title:
--   Active Branch Data: singleton growth eq singleton Growth
-- statement:
--   The Active Branch Data construction uses the singleton growth eq singleton Growth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedRemainder.lean#L123-L128
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedRemainder.lean#L123-L128

import Definitions.Def_BKAR_OrderedRecursion
import Definitions.Def_BKAR_OrderedRemainder
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveBranchData
variable {F : Forest V}

theorem BKAR.Forest.ActiveBranchData.singleton_growth_eq_singletonGrowth
    (extensions : ∀ e : {e // e ∈ F.activeEdges},
      ActiveExtension F e.val)
    (e : {e // e ∈ F.activeEdges}) :
    (singleton extensions).growth e = (extensions e).singletonGrowth := by sorry
