-- Prove2me | Theorems.Thm_BKAR_OrderedSimplexParams_head_le_top
-- name    : BKAR.OrderedSimplexParams.head_le_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:28:25.1528+00:00
-- url     : https://prove2.me/theorems/2e6a79d0-1ea1-5f58-bf7b-e8cb2ec2a9a1
-- title:
--   Ordered Simplex Params: head le top
-- statement:
--   The Ordered Simplex Params construction uses the head le top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedSimplex.lean#L100-L103
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedSimplex.lean#L100-L103

import Definitions.Def_BKAR_OrderedForest
import Definitions.Def_BKAR_OrderedSimplex
set_option autoImplicit false
noncomputable section
open BKAR
variable {V : Type*} [DecidableEq V]
open BKAR.OrderedSimplexParams

theorem BKAR.OrderedSimplexParams.head_le_top {top t : ℝ} {ts : List ℝ}
    (h : OrderedSimplexParams top (t :: ts)) :
    t ≤ top := by sorry
