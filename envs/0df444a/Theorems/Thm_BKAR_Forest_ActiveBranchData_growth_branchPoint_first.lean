-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveBranchData_growth_branchPoint_first
-- name    : BKAR.Forest.ActiveBranchData.growth_branchPoint_first
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:21:24.301924+00:00
-- url     : https://prove2.me/theorems/bfc2a720-263d-52f7-8820-abd8a0476b62
-- title:
--   Active Branch Data: growth branch Point first
-- statement:
--   The Active Branch Data construction uses the growth branch Point first property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedRemainder.lean#L98-L102
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedRemainder.lean#L98-L102

import Definitions.Def_BKAR_OrderedRecursion
import Definitions.Def_BKAR_OrderedRemainder
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveBranchData
variable {F : Forest V}

theorem BKAR.Forest.ActiveBranchData.growth_branchPoint_first (data : ActiveBranchData F)
    (e : {e // e ∈ F.activeEdges})
    (u : F.EdgeParam → ℝ) (t : ℝ) (ts : List ℝ) :
    (data.growth e).branchPoint u (t :: ts) e.val = t := by sorry
