-- Prove2me | Theorems.Thm_BKAR_OrderedSimplexParams_head_nonneg
-- name    : BKAR.OrderedSimplexParams.head_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:29:51.929803+00:00
-- url     : https://prove2.me/theorems/b41053c6-85b8-5ac0-a4cb-eefccf946b7e
-- title:
--   Ordered Simplex Params: head nonneg
-- statement:
--   The Ordered Simplex Params construction uses the head nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedSimplex.lean#L95-L98
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedSimplex.lean#L95-L98

import Definitions.Def_BKAR_OrderedForest
import Definitions.Def_BKAR_OrderedSimplex
set_option autoImplicit false
noncomputable section
open BKAR
variable {V : Type*} [DecidableEq V]
open BKAR.OrderedSimplexParams

theorem BKAR.OrderedSimplexParams.head_nonneg {top t : ℝ} {ts : List ℝ}
    (h : OrderedSimplexParams top (t :: ts)) :
    0 ≤ t := by sorry
