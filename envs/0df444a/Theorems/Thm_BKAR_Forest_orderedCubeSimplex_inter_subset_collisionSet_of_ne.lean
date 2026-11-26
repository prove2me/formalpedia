-- Prove2me | Theorems.Thm_BKAR_Forest_orderedCubeSimplex_inter_subset_collisionSet_of_ne
-- name    : BKAR.Forest.orderedCubeSimplex_inter_subset_collisionSet_of_ne
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:51:43.926257+00:00
-- url     : https://prove2.me/theorems/5afe3209-3216-5a48-aeb1-3cc6dfbdd347
-- title:
--   Forest: ordered Cube Simplex inter subset collision Set of ne
-- statement:
--   Distinct closed ordered cube sectors only overlap on the collision locus.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/MeasurePartition.lean#L190-L200
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/MeasurePartition.lean#L190-L200

import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Definitions.Def_BKAR_CubePartition_CubeIntegral
import Definitions.Def_BKAR_CubePartition_MeasurePartition
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.orderedCubeSimplex_inter_subset_collisionSet_of_ne
    (F : Forest V) {order₁ order₂ : List (Edge V)}
    (horder₁ : order₁ ∈ F.edgeOrders) (horder₂ : order₂ ∈ F.edgeOrders)
    (hne : order₁ ≠ order₂) :
    F.orderedCubeSimplex order₁ ∩ F.orderedCubeSimplex order₂ ⊆
      F.collisionSet := by sorry
