-- Prove2me | Theorems.Thm_BKAR_Forest_integral_unitCube_eq_sum_orderedCubeSimplex
-- name    : BKAR.Forest.integral_unitCube_eq_sum_orderedCubeSimplex
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:02:28.873634+00:00
-- url     : https://prove2.me/theorems/94af65eb-b31e-5948-8f6d-3724079460aa
-- title:
--   Forest: integral unit Cube eq sum ordered Cube Simplex
-- statement:
--   Finite-sum form of `Forest.integral_unitCube_eq_tsum_orderedCubeSimplex`.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/MeasurePartition.lean#L309-L321
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/MeasurePartition.lean#L309-L321

import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Definitions.Def_BKAR_CubePartition_CubeIntegral
import Definitions.Def_BKAR_CubePartition_MeasurePartition
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.integral_unitCube_eq_sum_orderedCubeSimplex
    (F : Forest V) (f : (F.EdgeParam → ℝ) → ℝ)
    (hfi : IntegrableOn f F.unitCube
      (volume : Measure (F.EdgeParam → ℝ))) :
    ∫ u in F.unitCube, f u ∂(volume : Measure (F.EdgeParam → ℝ)) =
      Finset.sum
        (Finset.univ :
          Finset {order : List (Edge V) // order ∈ F.edgeOrders})
        (fun order =>
          ∫ u in F.orderedCubeSimplex order.val, f u
            ∂(volume : Measure (F.EdgeParam → ℝ))) := by sorry
