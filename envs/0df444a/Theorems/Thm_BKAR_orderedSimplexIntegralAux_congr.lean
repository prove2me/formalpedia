-- Prove2me | Theorems.Thm_BKAR_orderedSimplexIntegralAux_congr
-- name    : BKAR.orderedSimplexIntegralAux_congr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:30:25.641921+00:00
-- url     : https://prove2.me/theorems/9158c471-fa14-4325-86fa-0f353ecb6041
-- title:
--   BKAR: ordered Simplex Integral Aux congr
-- statement:
--   The BKAR construction uses the ordered Simplex Integral Aux congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedSimplex.lean#L145-L157
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedSimplex.lean#L145-L157

import Definitions.Def_BKAR_OrderedForest
import Definitions.Def_BKAR_OrderedSimplex
set_option autoImplicit false
noncomputable section
open BKAR
variable {V : Type*} [DecidableEq V]

theorem BKAR.orderedSimplexIntegralAux_congr (top : ℝ) :
    ∀ (order : List (Edge V)) {f g : List ℝ → ℝ},
      (∀ ts, f ts = g ts) →
        orderedSimplexIntegralAux top order f =
          orderedSimplexIntegralAux top order g
  := by sorry
