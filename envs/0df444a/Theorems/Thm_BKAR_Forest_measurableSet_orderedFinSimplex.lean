-- Prove2me | Theorems.Thm_BKAR_Forest_measurableSet_orderedFinSimplex
-- name    : BKAR.Forest.measurableSet_orderedFinSimplex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:10:15.227145+00:00
-- url     : https://prove2.me/theorems/a07044e2-2ef4-4583-9f68-4c46d80c5f2b
-- title:
--   Forest: measurable Set ordered Fin Simplex
-- statement:
--   The finite ordered simplex sector in coordinate space is measurable.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Finite.lean#L471-L480
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Finite.lean#L471-L480

import Definitions.Def_BKAR_CubePartition_SimplexSector
import Definitions.Def_BKAR_CubePartition_SimplexSector_Finite
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]
omit [Fintype V] [DecidableEq V]

theorem BKAR.Forest.measurableSet_orderedFinSimplex (n : ℕ) :
    MeasurableSet (orderedFinSimplex n) := by sorry
