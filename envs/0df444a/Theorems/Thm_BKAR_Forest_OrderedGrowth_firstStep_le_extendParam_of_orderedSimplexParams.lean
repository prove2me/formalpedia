-- Prove2me | Theorems.Thm_BKAR_Forest_OrderedGrowth_firstStep_le_extendParam_of_orderedSimplexParams
-- name    : BKAR.Forest.OrderedGrowth.firstStep_le_extendParam_of_orderedSimplexParams
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:37:40.780987+00:00
-- url     : https://prove2.me/theorems/77deac92-387c-544f-9256-e99d1ab5fcb8
-- title:
--   Ordered Growth: first Step le extend Param of ordered Simplex Params
-- statement:
--   The Ordered Growth construction uses the first Step le extend Param of ordered Simplex Params property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedParams.lean#L125-L131
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedParams.lean#L125-L131

import Definitions.Def_BKAR_OrderedSimplex
import Definitions.Def_BKAR_OrderedParams
set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}

theorem BKAR.Forest.OrderedGrowth.firstStep_le_extendParam_of_orderedSimplexParams
    (h : OrderedGrowth F (e :: order) G) (u : F.EdgeParam → ℝ)
    {top t : ℝ} {ts : List ℝ}
    (hts : OrderedSimplexParams top (t :: ts))
    (hu : ∀ e : F.EdgeParam, top ≤ u e) :
    ∀ e' : h.tailForest.EdgeParam, t ≤ h.firstStep.extendParam u t e' := by sorry
