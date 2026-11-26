-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_growth_support_edges_eq_toFinset_union
-- name    : BKAR.Forest.ActiveTerminalBranchData.growth_support_edges_eq_toFinset_union
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:25:19.203555+00:00
-- url     : https://prove2.me/theorems/659ad87a-dd78-4698-a856-987bdc342b97
-- title:
--   Active Terminal Branch Data: growth support edges eq to Finset union
-- statement:
--   The Active Terminal Branch Data construction uses the growth support edges eq to Finset union property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean#L437-L442
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean#L437-L442

import Definitions.Def_BKAR_OrderedRemainder
import Definitions.Def_BKAR_OrderedTerminalGrowth
import Theorems.Thm_BKAR_OrderedSimplexParams_tail

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveTerminalBranchData
variable {F : Forest V}

theorem BKAR.Forest.ActiveTerminalBranchData.growth_support_edges_eq_toFinset_union
    (data : ActiveTerminalBranchData F)
    (e : {e // e ∈ F.activeEdges}) :
    (data.growth e).support.edges =
      (e.val :: (data.tail e).order).toFinset ∪ F.edges := by sorry
