-- Prove2me | Theorems.Thm_BKAR_OrderedSimplexParams_le_top_of_mem
-- name    : BKAR.OrderedSimplexParams.le_top_of_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:28:37.490107+00:00
-- url     : https://prove2.me/theorems/6d17c411-758d-55f8-8886-3557745cab13
-- title:
--   Ordered Simplex Params: le top of mem
-- statement:
--   The Ordered Simplex Params construction uses the le top of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedSimplex.lean#L124-L136
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedSimplex.lean#L124-L136

import Definitions.Def_BKAR_OrderedForest
import Definitions.Def_BKAR_OrderedSimplex
set_option autoImplicit false
noncomputable section
open BKAR
variable {V : Type*} [DecidableEq V]
open BKAR.OrderedSimplexParams

theorem BKAR.OrderedSimplexParams.le_top_of_mem :
    ∀ {top : ℝ} {ts : List ℝ} {t : ℝ},
      OrderedSimplexParams top ts → t ∈ ts → t ≤ top
  := by sorry
