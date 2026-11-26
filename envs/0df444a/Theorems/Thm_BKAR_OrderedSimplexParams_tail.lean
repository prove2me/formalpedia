-- Prove2me | Theorems.Thm_BKAR_OrderedSimplexParams_tail
-- name    : BKAR.OrderedSimplexParams.tail
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:27:56.895448+00:00
-- url     : https://prove2.me/theorems/9f7c849e-9096-4e38-98c9-725cba878420
-- title:
--   Ordered Simplex Params: tail
-- statement:
--   The Ordered Simplex Params construction uses the tail property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedSimplex.lean#L105-L108
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedSimplex.lean#L105-L108

import Definitions.Def_BKAR_OrderedForest
import Definitions.Def_BKAR_OrderedSimplex
set_option autoImplicit false
noncomputable section
open BKAR
variable {V : Type*} [DecidableEq V]
open BKAR.OrderedSimplexParams

theorem BKAR.OrderedSimplexParams.tail {top t : ℝ} {ts : List ℝ}
    (h : OrderedSimplexParams top (t :: ts)) :
    OrderedSimplexParams t ts := by sorry
