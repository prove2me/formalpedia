-- Prove2me | Theorems.Thm_BKAR_OrderedSimplexParams_nonneg_of_mem
-- name    : BKAR.OrderedSimplexParams.nonneg_of_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:30:00.351912+00:00
-- url     : https://prove2.me/theorems/a8e8d197-e5b1-5190-820e-2b0435c2579c
-- title:
--   Ordered Simplex Params: nonneg of mem
-- statement:
--   The Ordered Simplex Params construction uses the nonneg of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedSimplex.lean#L110-L122
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedSimplex.lean#L110-L122

import Definitions.Def_BKAR_OrderedForest
import Definitions.Def_BKAR_OrderedSimplex
set_option autoImplicit false
noncomputable section
open BKAR
variable {V : Type*} [DecidableEq V]
open BKAR.OrderedSimplexParams

theorem BKAR.OrderedSimplexParams.nonneg_of_mem :
    ∀ {top : ℝ} {ts : List ℝ} {t : ℝ},
      OrderedSimplexParams top ts → t ∈ ts → 0 ≤ t
  := by sorry
