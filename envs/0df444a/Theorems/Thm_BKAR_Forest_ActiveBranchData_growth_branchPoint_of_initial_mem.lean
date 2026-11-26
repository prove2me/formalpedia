-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveBranchData_growth_branchPoint_of_initial_mem
-- name    : BKAR.Forest.ActiveBranchData.growth_branchPoint_of_initial_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:21:27.683775+00:00
-- url     : https://prove2.me/theorems/ca9eb68a-d8dd-5939-b283-f5b492fb5ecd
-- title:
--   Active Branch Data: growth branch Point of initial mem
-- statement:
--   The Active Branch Data construction uses the growth branch Point of initial mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedRemainder.lean#L104-L110
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedRemainder.lean#L104-L110

import Definitions.Def_BKAR_OrderedRecursion
import Definitions.Def_BKAR_OrderedRemainder
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveBranchData
variable {F : Forest V}

theorem BKAR.Forest.ActiveBranchData.growth_branchPoint_of_initial_mem (data : ActiveBranchData F)
    (e : {e // e ∈ F.activeEdges})
    (u : F.EdgeParam → ℝ) (ts : List ℝ) {e' : Edge V}
    (he' : e' ∈ F.edges) :
    (data.growth e).branchPoint u ts e' = u ⟨e', he'⟩ := by sorry
