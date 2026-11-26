-- Prove2me | Theorems.Thm_BKAR_Forest_OrderedGrowth_derivativeOrder_cons
-- name    : BKAR.Forest.OrderedGrowth.derivativeOrder_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:35:45.752348+00:00
-- url     : https://prove2.me/theorems/38b2fb85-4e6c-43d6-b1d4-533cfc5b912f
-- title:
--   Ordered Growth: derivative Order cons
-- statement:
--   The Ordered Growth construction uses the derivative Order cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedBranch.lean#L148-L153
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedBranch.lean#L148-L153

import Definitions.Def_BKAR_OrderedParams
import Definitions.Def_BKAR_OrderedBranch
import Theorems.Thm_BKAR_OrderedSimplexParams_tail

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}

theorem BKAR.Forest.OrderedGrowth.derivativeOrder_cons {F F' G : Forest V} {e : Edge V}
    {order : List (Edge V)} (step : EdgeExtension F F' e)
    (tail : OrderedGrowth F' order G) :
    (OrderedGrowth.cons step tail).derivativeOrder =
      tail.derivativeOrder ++ [e] := by sorry
