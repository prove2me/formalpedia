-- Prove2me | Theorems.Thm_BKAR_Forest_pairCoordOfOrder_pairMeasurableEquivOfPair_symm
-- name    : BKAR.Forest.pairCoordOfOrder_pairMeasurableEquivOfPair_symm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:10:27.21119+00:00
-- url     : https://prove2.me/theorems/6591959e-8af8-4b14-aa75-7fe0109cee81
-- title:
--   Forest: pair Coord Of Order pair Measurable Equiv Of Pair symm
-- statement:
--   The Forest construction uses the pair Coord Of Order pair Measurable Equiv Of Pair symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Pair.lean#L250-L258
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Pair.lean#L250-L258

import Definitions.Def_BKAR_CubePartition_SimplexSector_Equiv
import Definitions.Def_BKAR_CubePartition_SimplexSector_Pair
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.pairCoordOfOrder_pairMeasurableEquivOfPair_symm
    (F : Forest V) {e₁ e₂ : Edge V}
    (hedges : F.edges = ({e₁, e₂} : Finset (Edge V))) (hne : e₁ ≠ e₂)
    (z : ℝ × ℝ) :
    F.pairCoordOfOrder e₁ e₂
        ((F.pairMeasurableEquivOfPair hedges hne).symm z) = z := by sorry
