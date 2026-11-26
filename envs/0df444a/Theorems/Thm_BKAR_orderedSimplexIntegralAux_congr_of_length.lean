-- Prove2me | Theorems.Thm_BKAR_orderedSimplexIntegralAux_congr_of_length
-- name    : BKAR.orderedSimplexIntegralAux_congr_of_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:30:18.919691+00:00
-- url     : https://prove2.me/theorems/98a3f00a-3748-4030-8873-1938dbd84db0
-- title:
--   BKAR: ordered Simplex Integral Aux congr of length
-- statement:
--   Congruence for nested simplex integrals when the integrands agree on
--   parameter lists whose length matches the remaining edge order.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedSimplex.lean#L169-L181
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedSimplex.lean#L169-L181

import Definitions.Def_BKAR_OrderedForest
import Definitions.Def_BKAR_OrderedSimplex
set_option autoImplicit false
noncomputable section
open BKAR
variable {V : Type*} [DecidableEq V]

theorem BKAR.orderedSimplexIntegralAux_congr_of_length (top : ℝ) :
    ∀ (order : List (Edge V)) {f g : List ℝ → ℝ},
      (∀ ts, ts.length = order.length → f ts = g ts) →
        orderedSimplexIntegralAux top order f =
          orderedSimplexIntegralAux top order g
  := by sorry
