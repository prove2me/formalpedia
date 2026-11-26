-- Prove2me | Theorems.Thm_BKAR_Forest_eq_of_mem_orderedCubeSimplex_of_notMem_collisionSet
-- name    : BKAR.Forest.eq_of_mem_orderedCubeSimplex_of_notMem_collisionSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:51:19.013928+00:00
-- url     : https://prove2.me/theorems/131f8a95-7c2d-5bc8-b244-17e1967d4d3d
-- title:
--   Forest: eq of mem ordered Cube Simplex of not Mem collision Set
-- statement:
--   Away from collision hyperplanes, membership in two closed ordered sectors
--   forces the two canonical edge orders to be equal.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/MeasurePartition.lean#L158-L187
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/MeasurePartition.lean#L158-L187

import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Definitions.Def_BKAR_CubePartition_CubeIntegral
import Definitions.Def_BKAR_CubePartition_MeasurePartition
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.eq_of_mem_orderedCubeSimplex_of_notMem_collisionSet
    (F : Forest V) {order₁ order₂ : List (Edge V)}
    (horder₁ : order₁ ∈ F.edgeOrders) (horder₂ : order₂ ∈ F.edgeOrders)
    {u : F.EdgeParam → ℝ}
    (hno : u ∉ F.collisionSet)
    (hu₁ : u ∈ F.orderedCubeSimplex order₁)
    (hu₂ : u ∈ F.orderedCubeSimplex order₂) :
    order₁ = order₂ := by sorry
