-- Prove2me | Theorems.Thm_BKAR_Forest_OrderedGrowth_first_mem_activeEdges
-- name    : BKAR.Forest.OrderedGrowth.first_mem_activeEdges
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:35:17.895655+00:00
-- url     : https://prove2.me/theorems/7f020f56-72d6-4f80-8a28-7bec25e3044a
-- title:
--   Ordered Growth: first mem active Edges
-- statement:
--   The Ordered Growth construction uses the first mem active Edges property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedForest.lean#L66-L68
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedForest.lean#L66-L68

import Definitions.Def_BKAR_OrderedExpansion
import Definitions.Def_BKAR_OrderedForest
set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}

theorem BKAR.Forest.OrderedGrowth.first_mem_activeEdges (h : OrderedGrowth F (e :: order) G) :
    e ∈ F.activeEdges := by sorry
