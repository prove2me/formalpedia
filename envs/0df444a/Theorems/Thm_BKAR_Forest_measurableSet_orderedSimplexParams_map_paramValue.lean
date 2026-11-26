-- Prove2me | Theorems.Thm_BKAR_Forest_measurableSet_orderedSimplexParams_map_paramValue
-- name    : BKAR.Forest.measurableSet_orderedSimplexParams_map_paramValue
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:02:33.552261+00:00
-- url     : https://prove2.me/theorems/e6927bd4-f328-4cfd-a223-a6dfcdb6075a
-- title:
--   Forest: measurable Set ordered Simplex Params map param Value
-- statement:
--   The Forest construction uses the measurable Set ordered Simplex Params map param Value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/MeasurePartition.lean#L256-L277
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/MeasurePartition.lean#L256-L277

import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Definitions.Def_BKAR_CubePartition_CubeIntegral
import Definitions.Def_BKAR_CubePartition_MeasurePartition
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.measurableSet_orderedSimplexParams_map_paramValue
    (F : Forest V) :
    ∀ (order : List (Edge V))
      {topFn : (F.EdgeParam → ℝ) → ℝ},
      Measurable topFn →
      MeasurableSet
        {u : F.EdgeParam → ℝ |
          OrderedSimplexParams (topFn u)
            (order.map (F.paramValue u))}
  := by sorry
