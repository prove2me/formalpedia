-- Prove2me | Theorems.Thm_BKAR_Forest_OrderedGrowth_params_initial
-- name    : BKAR.Forest.OrderedGrowth.params_initial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:30:41.5108+00:00
-- url     : https://prove2.me/theorems/aac9b50c-bcc8-4bf3-bde5-b68576b1a013
-- title:
--   Ordered Growth: params initial
-- statement:
--   Ordered-growth parameters preserve every edge parameter already present at the start.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedParams.lean#L134-L161
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedParams.lean#L134-L161

import Definitions.Def_BKAR_OrderedSimplex
import Definitions.Def_BKAR_OrderedParams
import Theorems.Thm_BKAR_Forest_OrderedGrowth_initial_edges_subset_edges

set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}

theorem BKAR.Forest.OrderedGrowth.params_initial (h : OrderedGrowth F order G)
    (u : F.EdgeParam → ℝ) (ts : List ℝ) (e : F.EdgeParam) :
    h.params u ts ⟨e.val, h.initial_edges_subset_edges e.property⟩ = u e := by sorry
