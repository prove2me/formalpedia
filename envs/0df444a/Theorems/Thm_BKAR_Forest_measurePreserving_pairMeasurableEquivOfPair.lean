-- Prove2me | Theorems.Thm_BKAR_Forest_measurePreserving_pairMeasurableEquivOfPair
-- name    : BKAR.Forest.measurePreserving_pairMeasurableEquivOfPair
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:58:01.168824+00:00
-- url     : https://prove2.me/theorems/45a3257c-1527-59bc-9109-76249c36191b
-- title:
--   Forest: measure Preserving pair Measurable Equiv Of Pair
-- statement:
--   The Forest construction uses the measure Preserving pair Measurable Equiv Of Pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Pair.lean#L230-L248
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Pair.lean#L230-L248

import Definitions.Def_BKAR_CubePartition_SimplexSector_Equiv
import Definitions.Def_BKAR_CubePartition_SimplexSector_Pair
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.measurePreserving_pairMeasurableEquivOfPair
    (F : Forest V) {e₁ e₂ : Edge V}
    (hedges : F.edges = ({e₁, e₂} : Finset (Edge V))) (hne : e₁ ≠ e₂) :
    MeasurePreserving (F.pairMeasurableEquivOfPair hedges hne)
      (volume : Measure (F.EdgeParam → ℝ)) (volume : Measure (ℝ × ℝ)) := by sorry
