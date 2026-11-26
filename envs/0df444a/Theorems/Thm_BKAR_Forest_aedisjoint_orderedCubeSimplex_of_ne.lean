-- Prove2me | Theorems.Thm_BKAR_Forest_aedisjoint_orderedCubeSimplex_of_ne
-- name    : BKAR.Forest.aedisjoint_orderedCubeSimplex_of_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:51:44.046464+00:00
-- url     : https://prove2.me/theorems/a55fc079-80a5-5ab9-82f6-8cce5b285172
-- title:
--   Forest: aedisjoint ordered Cube Simplex of ne
-- statement:
--   Distinct canonical ordered cube sectors are a.e. disjoint.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/MeasurePartition.lean#L203-L211
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/MeasurePartition.lean#L203-L211

import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Definitions.Def_BKAR_CubePartition_CubeIntegral
import Definitions.Def_BKAR_CubePartition_MeasurePartition
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.aedisjoint_orderedCubeSimplex_of_ne
    (F : Forest V) {order₁ order₂ : List (Edge V)}
    (horder₁ : order₁ ∈ F.edgeOrders) (horder₂ : order₂ ∈ F.edgeOrders)
    (hne : order₁ ≠ order₂) :
    AEDisjoint (volume : Measure (F.EdgeParam → ℝ))
      (F.orderedCubeSimplex order₁) (F.orderedCubeSimplex order₂) := by sorry
