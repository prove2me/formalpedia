-- Prove2me | Theorems.Thm_BKAR_Forest_OrderedGrowth_tailGrowth_edges_eq_toFinset_union
-- name    : BKAR.Forest.OrderedGrowth.tailGrowth_edges_eq_toFinset_union
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:36:02.059459+00:00
-- url     : https://prove2.me/theorems/801c0910-1d52-469b-bfed-87f153f0fa65
-- title:
--   Ordered Growth: tail Growth edges eq to Finset union
-- statement:
--   The Ordered Growth construction uses the tail Growth edges eq to Finset union property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedForest.lean#L93-L96
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedForest.lean#L93-L96

import Definitions.Def_BKAR_OrderedExpansion
import Definitions.Def_BKAR_OrderedForest
set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}

theorem BKAR.Forest.OrderedGrowth.tailGrowth_edges_eq_toFinset_union
    (h : OrderedGrowth F (e :: order) G) :
    G.edges = order.toFinset ∪ h.tailForest.edges := by sorry
