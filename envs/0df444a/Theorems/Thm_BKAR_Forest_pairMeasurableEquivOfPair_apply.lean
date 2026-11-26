-- Prove2me | Theorems.Thm_BKAR_Forest_pairMeasurableEquivOfPair_apply
-- name    : BKAR.Forest.pairMeasurableEquivOfPair_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:57:54.97379+00:00
-- url     : https://prove2.me/theorems/77e4bfd8-187a-5697-924a-24eb9b538b6c
-- title:
--   Forest: pair Measurable Equiv Of Pair apply
-- statement:
--   The Forest construction uses the pair Measurable Equiv Of Pair apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Pair.lean#L196-L228
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Pair.lean#L196-L228

import Definitions.Def_BKAR_CubePartition_SimplexSector_Equiv
import Definitions.Def_BKAR_CubePartition_SimplexSector_Pair
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.pairMeasurableEquivOfPair_apply
    (F : Forest V) {e₁ e₂ : Edge V}
    (hedges : F.edges = ({e₁, e₂} : Finset (Edge V))) (hne : e₁ ≠ e₂)
    (u : F.EdgeParam → ℝ) :
    F.pairMeasurableEquivOfPair hedges hne u =
      F.pairCoordOfOrder e₁ e₂ u := by sorry
