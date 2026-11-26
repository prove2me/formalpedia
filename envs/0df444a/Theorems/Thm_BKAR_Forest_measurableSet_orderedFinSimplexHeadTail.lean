-- Prove2me | Theorems.Thm_BKAR_Forest_measurableSet_orderedFinSimplexHeadTail
-- name    : BKAR.Forest.measurableSet_orderedFinSimplexHeadTail
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:11:51.654857+00:00
-- url     : https://prove2.me/theorems/1d4e646f-ee7e-4dd1-a6bd-1e63c2c59a8a
-- title:
--   Forest: measurable Set ordered Fin Simplex Head Tail
-- statement:
--   The head-tail ordered simplex sector is measurable.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Finite.lean#L222-L246
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Finite.lean#L222-L246

import Definitions.Def_BKAR_CubePartition_SimplexSector
import Definitions.Def_BKAR_CubePartition_SimplexSector_Finite
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]
omit [Fintype V] [DecidableEq V]

theorem BKAR.Forest.measurableSet_orderedFinSimplexHeadTail (top : ℝ) (n : ℕ) :
    MeasurableSet (orderedFinSimplexHeadTail top n) := by sorry
