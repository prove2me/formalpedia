-- Prove2me | Theorems.Thm_BKAR_Forest_OrderedGrowth_params_cons_cons
-- name    : BKAR.Forest.OrderedGrowth.params_cons_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:29:51.893996+00:00
-- url     : https://prove2.me/theorems/1558db70-8e44-490d-aebf-c749e8008587
-- title:
--   Ordered Growth: params cons cons
-- statement:
--   The Ordered Growth construction uses the params cons cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedParams.lean#L78-L84
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedParams.lean#L78-L84

import Definitions.Def_BKAR_OrderedSimplex
import Definitions.Def_BKAR_OrderedParams
import Theorems.Thm_BKAR_OrderedSimplexParams_tail

set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}

theorem BKAR.Forest.OrderedGrowth.params_cons_cons {F F' G : Forest V} {e : Edge V}
    {order : List (Edge V)} (step : EdgeExtension F F' e)
    (tail : OrderedGrowth F' order G) (u : F.EdgeParam → ℝ)
    (t : ℝ) (ts : List ℝ) :
    (OrderedGrowth.cons step tail).params u (t :: ts) =
      tail.params (step.extendParam u t) ts := by sorry

attribute [defeq] BKAR.Forest.OrderedGrowth.params_cons_cons
