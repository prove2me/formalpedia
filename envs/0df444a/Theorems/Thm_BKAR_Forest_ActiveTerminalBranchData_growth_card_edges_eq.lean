-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_growth_card_edges_eq
-- name    : BKAR.Forest.ActiveTerminalBranchData.growth_card_edges_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:25:12.324677+00:00
-- url     : https://prove2.me/theorems/5dbc8851-5f4d-598b-aa2b-baeaee5a44fd
-- title:
--   Active Terminal Branch Data: growth card edges eq
-- statement:
--   The Active Terminal Branch Data construction uses the growth card edges eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean#L449-L453
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean#L449-L453

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

theorem BKAR.Forest.ActiveTerminalBranchData.growth_card_edges_eq (data : ActiveTerminalBranchData F)
    (e : {e // e ∈ F.activeEdges}) :
    (data.growth e).terminal.edges.card =
      F.edges.card + (e.val :: (data.tail e).order).length := by sorry
