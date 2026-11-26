-- Prove2me | Theorems.Thm_BKAR_Forest_OrderedGrowth_params_cons_nil
-- name    : BKAR.Forest.OrderedGrowth.params_cons_nil
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:29:50.939857+00:00
-- url     : https://prove2.me/theorems/6343ce5a-10cb-4b8c-9dae-2ef510f80828
-- title:
--   Ordered Growth: params cons nil
-- statement:
--   The Ordered Growth construction uses the params cons nil property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedParams.lean#L70-L75
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedParams.lean#L70-L75

import Definitions.Def_BKAR_OrderedSimplex
import Definitions.Def_BKAR_OrderedParams
import Theorems.Thm_BKAR_OrderedSimplexParams_tail

set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}

theorem BKAR.Forest.OrderedGrowth.params_cons_nil {F F' G : Forest V} {e : Edge V}
    {order : List (Edge V)} (step : EdgeExtension F F' e)
    (tail : OrderedGrowth F' order G) (u : F.EdgeParam → ℝ) :
    (OrderedGrowth.cons step tail).params u [] =
      tail.params (step.extendParam u 0) [] := by sorry

attribute [defeq] BKAR.Forest.OrderedGrowth.params_cons_nil
