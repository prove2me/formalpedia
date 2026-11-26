-- Prove2me | Theorems.Thm_BKAR_Forest_pairwise_sectorOrderRel_of_orderedSimplexParams
-- name    : BKAR.Forest.pairwise_sectorOrderRel_of_orderedSimplexParams
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:51:02.205518+00:00
-- url     : https://prove2.me/theorems/336ad90f-2fc5-4a25-923e-e166d1e33b19
-- title:
--   Forest: pairwise sector Order Rel of ordered Simplex Params
-- statement:
--   The Forest construction uses the pairwise sector Order Rel of ordered Simplex Params property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/MeasurePartition.lean#L132-L152
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/MeasurePartition.lean#L132-L152

import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Definitions.Def_BKAR_CubePartition_CubeIntegral
import Definitions.Def_BKAR_CubePartition_MeasurePartition
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.pairwise_sectorOrderRel_of_orderedSimplexParams
    (F : Forest V) (u : F.EdgeParam → ℝ) :
    ∀ (order : List (Edge V)) {top : ℝ},
      (∀ e ∈ order, e ∈ F.edges) →
      OrderedSimplexParams top (order.map (F.paramValue u)) →
      order.Pairwise (F.sectorOrderRel u)
  := by sorry
