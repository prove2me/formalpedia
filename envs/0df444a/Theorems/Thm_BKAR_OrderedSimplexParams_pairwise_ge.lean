-- Prove2me | Theorems.Thm_BKAR_OrderedSimplexParams_pairwise_ge
-- name    : BKAR.OrderedSimplexParams.pairwise_ge
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:32:33.102619+00:00
-- url     : https://prove2.me/theorems/7f48e55d-44e7-5b93-9953-7f28311db7e1
-- title:
--   Ordered Simplex Params: pairwise ge
-- statement:
--   The Ordered Simplex Params construction uses the pairwise ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/MeasurePartition.lean#L21-L32
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/MeasurePartition.lean#L21-L32

import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Definitions.Def_BKAR_CubePartition_CubeIntegral
import Definitions.Def_BKAR_CubePartition_MeasurePartition
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.OrderedSimplexParams

theorem BKAR.OrderedSimplexParams.pairwise_ge :
    ∀ {top : ℝ} {ts : List ℝ},
      OrderedSimplexParams top ts →
        ts.Pairwise fun t s => s ≤ t
  := by sorry
