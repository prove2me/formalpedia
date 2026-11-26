-- Prove2me | Theorems.Thm_BKAR_Forest_EdgeExtension_activeEdges_card_lt
-- name    : BKAR.Forest.EdgeExtension.activeEdges_card_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:27:03.178802+00:00
-- url     : https://prove2.me/theorems/53748c3f-f099-595f-bf6d-dcd2fc589720
-- title:
--   Edge Extension: active Edges card lt
-- statement:
--   A one-edge extension strictly decreases the number of active edges.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedExpansion.lean#L56-L61
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedExpansion.lean#L56-L61

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_BKAR_ForestGraph
import Definitions.Def_BKAR_Differential
import Definitions.Def_BKAR_OrderedExpansion
set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.EdgeExtension
variable {F F' : Forest V} {e₀ : Edge V}

theorem BKAR.Forest.EdgeExtension.activeEdges_card_lt (h : EdgeExtension F F' e₀) :
    F'.activeEdges.card < F.activeEdges.card := by sorry
