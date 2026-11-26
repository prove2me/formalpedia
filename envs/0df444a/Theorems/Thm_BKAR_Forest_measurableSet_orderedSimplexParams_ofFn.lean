-- Prove2me | Theorems.Thm_BKAR_Forest_measurableSet_orderedSimplexParams_ofFn
-- name    : BKAR.Forest.measurableSet_orderedSimplexParams_ofFn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:10:46.387315+00:00
-- url     : https://prove2.me/theorems/6bb48db9-9d78-5f51-adf6-49e401f2fad1
-- title:
--   Forest: measurable Set ordered Simplex Params of Fn
-- statement:
--   The ordered-simplex predicate on `Fin n` coordinate tuples is measurable.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Finite.lean#L83-L98
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Finite.lean#L83-L98

import Definitions.Def_BKAR_CubePartition_SimplexSector
import Definitions.Def_BKAR_CubePartition_SimplexSector_Finite
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]
omit [Fintype V] [DecidableEq V]

theorem BKAR.Forest.measurableSet_orderedSimplexParams_ofFn (n : ℕ) :
    MeasurableSet
      {ts : Fin n → ℝ | OrderedSimplexParams 1 (List.ofFn ts)} := by sorry
