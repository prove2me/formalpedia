-- Prove2me | Theorems.Thm_BKAR_Forest_pairwise_aedisjoint_orderedCubeSimplex
-- name    : BKAR.Forest.pairwise_aedisjoint_orderedCubeSimplex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:51:54.842917+00:00
-- url     : https://prove2.me/theorems/8f0dd97d-25f7-5ffc-9d28-05390ed1dfba
-- title:
--   Forest: pairwise aedisjoint ordered Cube Simplex
-- statement:
--   The canonical ordered cube sectors are pairwise a.e. disjoint.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/MeasurePartition.lean#L214-L223
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/MeasurePartition.lean#L214-L223

import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Definitions.Def_BKAR_CubePartition_CubeIntegral
import Definitions.Def_BKAR_CubePartition_MeasurePartition
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.pairwise_aedisjoint_orderedCubeSimplex (F : Forest V) :
    Pairwise
      (fun order₁ order₂ : {order : List (Edge V) // order ∈ F.edgeOrders} =>
        AEDisjoint (volume : Measure (F.EdgeParam → ℝ))
          (F.orderedCubeSimplex order₁.val)
          (F.orderedCubeSimplex order₂.val)) := by sorry
