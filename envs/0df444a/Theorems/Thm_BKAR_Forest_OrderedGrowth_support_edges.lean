-- Prove2me | Theorems.Thm_BKAR_Forest_OrderedGrowth_support_edges
-- name    : BKAR.Forest.OrderedGrowth.support_edges
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:36:03.246252+00:00
-- url     : https://prove2.me/theorems/171cd6d3-4d8c-59ae-a981-faa6eeb4bd21
-- title:
--   Ordered Growth: support edges
-- statement:
--   The Ordered Growth construction uses the support edges property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedForest.lean#L102-L104
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedForest.lean#L102-L104

import Definitions.Def_BKAR_OrderedExpansion
import Definitions.Def_BKAR_OrderedForest
import Theorems.Thm_BKAR_Forest_support_edges

set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}

theorem BKAR.Forest.OrderedGrowth.support_edges (h : OrderedGrowth F order G) :
    h.support.edges = G.edges := by sorry
