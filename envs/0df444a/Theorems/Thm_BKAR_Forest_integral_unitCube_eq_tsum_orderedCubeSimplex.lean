-- Prove2me | Theorems.Thm_BKAR_Forest_integral_unitCube_eq_tsum_orderedCubeSimplex
-- name    : BKAR.Forest.integral_unitCube_eq_tsum_orderedCubeSimplex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:02:28.799556+00:00
-- url     : https://prove2.me/theorems/68f5e34a-4e2d-5c6a-bec3-35eca29d0dd9
-- title:
--   Forest: integral unit Cube eq tsum ordered Cube Simplex
-- statement:
--   Almost-disjoint integral partition of the unit cube: once the closed sectors are
--   measurable and the integrand is integrable on the cube, the integral over the
--   unit cube is the sum of the sector integrals. The a.e. disjointness comes from
--   the collision-hyperplane theorem above.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/MeasurePartition.lean#L293-L306
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/MeasurePartition.lean#L293-L306

import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Definitions.Def_BKAR_CubePartition_CubeIntegral
import Definitions.Def_BKAR_CubePartition_MeasurePartition
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.integral_unitCube_eq_tsum_orderedCubeSimplex
    (F : Forest V) (f : (F.EdgeParam → ℝ) → ℝ)
    (hfi : IntegrableOn f F.unitCube
      (volume : Measure (F.EdgeParam → ℝ))) :
    ∫ u in F.unitCube, f u ∂(volume : Measure (F.EdgeParam → ℝ)) =
      ∑' order : {order : List (Edge V) // order ∈ F.edgeOrders},
        ∫ u in F.orderedCubeSimplex order.val, f u
          ∂(volume : Measure (F.EdgeParam → ℝ)) := by sorry
