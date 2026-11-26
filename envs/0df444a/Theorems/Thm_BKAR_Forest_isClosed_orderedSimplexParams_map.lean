-- Prove2me | Theorems.Thm_BKAR_Forest_isClosed_orderedSimplexParams_map
-- name    : BKAR.Forest.isClosed_orderedSimplexParams_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:11:33.340081+00:00
-- url     : https://prove2.me/theorems/fe03ed30-d3b3-4de4-a025-b63e2082ffcd
-- title:
--   Forest: is Closed ordered Simplex Params map
-- statement:
--   Closedness of an ordered-simplex predicate evaluated on a finite list of
--   continuous real-valued coordinate functions.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Finite.lean#L58-L79
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Finite.lean#L58-L79

import Definitions.Def_BKAR_CubePartition_SimplexSector
import Definitions.Def_BKAR_CubePartition_SimplexSector_Finite
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]
omit [Fintype V] [DecidableEq V]

theorem BKAR.Forest.isClosed_orderedSimplexParams_map
    {α : Type*} [TopologicalSpace α] :
    ∀ (fs : List (α → ℝ)) {topFn : α → ℝ},
      Continuous topFn →
      (∀ f ∈ fs, Continuous f) →
      IsClosed
        {x : α | OrderedSimplexParams (topFn x) (fs.map fun f => f x)}
  := by sorry
