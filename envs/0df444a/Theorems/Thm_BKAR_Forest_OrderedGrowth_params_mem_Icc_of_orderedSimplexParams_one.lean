-- Prove2me | Theorems.Thm_BKAR_Forest_OrderedGrowth_params_mem_Icc_of_orderedSimplexParams_one
-- name    : BKAR.Forest.OrderedGrowth.params_mem_Icc_of_orderedSimplexParams_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:37:53.465266+00:00
-- url     : https://prove2.me/theorems/28486dd9-18ae-49d7-901f-26045b384579
-- title:
--   Ordered Growth: params mem Icc of ordered Simplex Params one
-- statement:
--   The Ordered Growth construction uses the params mem Icc of ordered Simplex Params one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedParams.lean#L117-L123
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedParams.lean#L117-L123

import Definitions.Def_BKAR_OrderedSimplex
import Definitions.Def_BKAR_OrderedParams
set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}

theorem BKAR.Forest.OrderedGrowth.params_mem_Icc_of_orderedSimplexParams_one
    (h : OrderedGrowth F order G) (u : F.EdgeParam → ℝ)
    {ts : List ℝ}
    (hu : ∀ e : F.EdgeParam, 0 ≤ u e ∧ u e ≤ 1)
    (hts : OrderedSimplexParams 1 ts) :
    ∀ e : G.EdgeParam, 0 ≤ h.params u ts e ∧ h.params u ts e ≤ 1 := by sorry
