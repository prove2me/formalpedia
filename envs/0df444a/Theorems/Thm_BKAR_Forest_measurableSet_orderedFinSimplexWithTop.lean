-- Prove2me | Theorems.Thm_BKAR_Forest_measurableSet_orderedFinSimplexWithTop
-- name    : BKAR.Forest.measurableSet_orderedFinSimplexWithTop
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:00:57.312913+00:00
-- url     : https://prove2.me/theorems/45fdf1b1-035c-409b-b40e-e31fd837130b
-- title:
--   Forest: measurable Set ordered Fin Simplex With Top
-- statement:
--   Variable-top finite ordered simplexes are measurable.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Finite.lean#L109-L123
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Finite.lean#L109-L123

import Definitions.Def_BKAR_CubePartition_SimplexSector
import Definitions.Def_BKAR_CubePartition_SimplexSector_Finite
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]
omit [Fintype V] [DecidableEq V]

theorem BKAR.Forest.measurableSet_orderedFinSimplexWithTop (top : ℝ) (n : ℕ) :
    MeasurableSet (orderedFinSimplexWithTop top n) := by sorry
