-- Prove2me | Theorems.Thm_BKAR_orderedSimplexIntegral_congr
-- name    : BKAR.orderedSimplexIntegral_congr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:37:17.837695+00:00
-- url     : https://prove2.me/theorems/6cc3edca-d602-5702-a8ea-11fcf21a9774
-- title:
--   BKAR: ordered Simplex Integral congr
-- statement:
--   The BKAR construction uses the ordered Simplex Integral congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedSimplex.lean#L159-L163
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedSimplex.lean#L159-L163

import Definitions.Def_BKAR_OrderedForest
import Definitions.Def_BKAR_OrderedSimplex
set_option autoImplicit false
noncomputable section
open BKAR
variable {V : Type*} [DecidableEq V]

theorem BKAR.orderedSimplexIntegral_congr {order : List (Edge V)}
    {f g : List ℝ → ℝ} (hfg : ∀ ts, f ts = g ts) :
    orderedSimplexIntegral order f = orderedSimplexIntegral order g := by sorry
