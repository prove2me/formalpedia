-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveExtension_activeEdges_card_lt
-- name    : BKAR.Forest.ActiveExtension.activeEdges_card_lt
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:34:12.585424+00:00
-- url     : https://prove2.me/theorems/d75c787c-ed8f-5332-bcd6-3b62dc1a6428
-- title:
--   Active Extension: active Edges card lt
-- statement:
--   A chosen active extension strictly decreases the number of active edges.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedExpansion.lean#L181-L183
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedExpansion.lean#L181-L183

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_BKAR_ForestGraph
import Definitions.Def_BKAR_Differential
import Definitions.Def_BKAR_OrderedExpansion
set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveExtension
variable {F : Forest V} {e : Edge V}

theorem BKAR.Forest.ActiveExtension.activeEdges_card_lt (h : ActiveExtension F e) :
    h.forest.activeEdges.card < F.activeEdges.card := by sorry
