-- Prove2me | Theorems.Thm_BKAR_Forest_measurableSet_orderedPairSector
-- name    : BKAR.Forest.measurableSet_orderedPairSector
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:58:07.653966+00:00
-- url     : https://prove2.me/theorems/7380de76-0f46-4459-8dd4-5a3026157ac3
-- title:
--   Forest: measurable Set ordered Pair Sector
-- statement:
--   The Forest construction uses the measurable Set ordered Pair Sector property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Pair.lean#L63-L77
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Pair.lean#L63-L77

import Definitions.Def_BKAR_CubePartition_SimplexSector_Equiv
import Definitions.Def_BKAR_CubePartition_SimplexSector_Pair
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.measurableSet_orderedPairSector : MeasurableSet orderedPairSector := by sorry
