-- Prove2me | Theorems.Thm_BKAR_orderedSimplexIntegral_congr_of_length
-- name    : BKAR.orderedSimplexIntegral_congr_of_length
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:37:24.815347+00:00
-- url     : https://prove2.me/theorems/d60c8568-aa6c-5fdc-812f-13944b5260e6
-- title:
--   BKAR: ordered Simplex Integral congr of length
-- statement:
--   Unit-bound version of `orderedSimplexIntegralAux_congr_of_length`.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedSimplex.lean#L186-L191
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedSimplex.lean#L186-L191

import Definitions.Def_BKAR_OrderedForest
import Definitions.Def_BKAR_OrderedSimplex
set_option autoImplicit false
noncomputable section
open BKAR
variable {V : Type*} [DecidableEq V]

theorem BKAR.orderedSimplexIntegral_congr_of_length {order : List (Edge V)}
    {f g : List ℝ → ℝ}
    (hfg : ∀ ts, ts.length = order.length → f ts = g ts) :
    orderedSimplexIntegral order f = orderedSimplexIntegral order g := by sorry
