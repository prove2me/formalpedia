-- Prove2me | Theorems.Thm_BKAR_Forest_measurableSet_orderedSimplexParams_map
-- name    : BKAR.Forest.measurableSet_orderedSimplexParams_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:00:17.078103+00:00
-- url     : https://prove2.me/theorems/68310f84-2fac-5a5b-837f-0c3899f243fa
-- title:
--   Forest: measurable Set ordered Simplex Params map
-- statement:
--   Generic measurability of an ordered-simplex predicate evaluated on a finite
--   list of measurable real-valued coordinate functions.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Finite.lean#L30-L51
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Finite.lean#L30-L51

import Definitions.Def_BKAR_CubePartition_SimplexSector
import Definitions.Def_BKAR_CubePartition_SimplexSector_Finite
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]
omit [Fintype V] [DecidableEq V]

theorem BKAR.Forest.measurableSet_orderedSimplexParams_map
    {α : Type*} [MeasurableSpace α] :
    ∀ (fs : List (α → ℝ)) {topFn : α → ℝ},
      Measurable topFn →
      (∀ f ∈ fs, Measurable f) →
      MeasurableSet
        {x : α | OrderedSimplexParams (topFn x) (fs.map fun f => f x)}
  := by sorry
