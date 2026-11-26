-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_growth_edges_eq_toFinset_union
-- name    : BKAR.Forest.ActiveTerminalBranchData.growth_edges_eq_toFinset_union
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:25:05.456855+00:00
-- url     : https://prove2.me/theorems/39dcf384-7c9c-4a12-89b2-d2e0ad62aa8f
-- title:
--   Active Terminal Branch Data: growth edges eq to Finset union
-- statement:
--   The Active Terminal Branch Data construction uses the growth edges eq to Finset union property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean#L431-L435
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean#L431-L435

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

theorem BKAR.Forest.ActiveTerminalBranchData.growth_edges_eq_toFinset_union (data : ActiveTerminalBranchData F)
    (e : {e // e ∈ F.activeEdges}) :
    (data.growth e).terminal.edges =
      (e.val :: (data.tail e).order).toFinset ∪ F.edges := by sorry
