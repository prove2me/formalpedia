-- Prove2me | Theorems.Thm_BKAR_Forest_OrderedGrowth_params_mem_Icc_of_orderedSimplexParams
-- name    : BKAR.Forest.OrderedGrowth.params_mem_Icc_of_orderedSimplexParams
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:30:28.851869+00:00
-- url     : https://prove2.me/theorems/ad30f897-2d2d-5ce7-ae91-8d2c5703d757
-- title:
--   Ordered Growth: params mem Icc of ordered Simplex Params
-- statement:
--   The Ordered Growth construction uses the params mem Icc of ordered Simplex Params property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedParams.lean#L108-L115
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedParams.lean#L108-L115

import Definitions.Def_BKAR_OrderedSimplex
import Definitions.Def_BKAR_OrderedParams
set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}

theorem BKAR.Forest.OrderedGrowth.params_mem_Icc_of_orderedSimplexParams (h : OrderedGrowth F order G)
    (u : F.EdgeParam → ℝ) {top : ℝ} {ts : List ℝ}
    (hu : ∀ e : F.EdgeParam, 0 ≤ u e ∧ u e ≤ 1)
    (htop : top ≤ 1) (hts : OrderedSimplexParams top ts) :
    ∀ e : G.EdgeParam, 0 ≤ h.params u ts e ∧ h.params u ts e ≤ 1 := by sorry
