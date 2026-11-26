-- Prove2me | Theorems.Thm_BKAR_Forest_OrderedGrowth_first_not_mem_edges
-- name    : BKAR.Forest.OrderedGrowth.first_not_mem_edges
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:29:27.469383+00:00
-- url     : https://prove2.me/theorems/f5be8688-ea90-58cf-9389-ed74bad2256a
-- title:
--   Ordered Growth: first not mem edges
-- statement:
--   The Ordered Growth construction uses the first not mem edges property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedForest.lean#L70-L72
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedForest.lean#L70-L72

import Definitions.Def_BKAR_OrderedExpansion
import Definitions.Def_BKAR_OrderedForest
set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}

theorem BKAR.Forest.OrderedGrowth.first_not_mem_edges (h : OrderedGrowth F (e :: order) G) :
    e ∉ F.edges := by sorry
