-- Prove2me | Theorems.Thm_BKAR_Forest_setIntegral_orderedCubeSimplex_eq_orderedFinSimplex_symm
-- name    : BKAR.Forest.setIntegral_orderedCubeSimplex_eq_orderedFinSimplex_symm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:12:39.188694+00:00
-- url     : https://prove2.me/theorems/a6a92cdf-e5ec-5eb8-825d-841067dc8134
-- title:
--   Forest: set Integral ordered Cube Simplex eq ordered Fin Simplex symm
-- statement:
--   Measure transport for arbitrary canonical orders, now for integrands written
--   on forest cube coordinates. This is the sector-side form needed by the final
--   simplex-sector conversion theorem.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Finite.lean#L557-L587
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Finite.lean#L557-L587

import Definitions.Def_BKAR_CubePartition_SimplexSector
import Definitions.Def_BKAR_CubePartition_SimplexSector_Finite
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.setIntegral_orderedCubeSimplex_eq_orderedFinSimplex_symm
    (F : Forest V) {order : List (Edge V)} (horder : order ∈ F.edgeOrders)
    (g : (F.EdgeParam → ℝ) → ℝ) :
    ∫ u in F.orderedCubeSimplex order, g u
        ∂(volume : Measure (F.EdgeParam → ℝ)) =
      ∫ ts in orderedFinSimplex order.length,
        g ((F.orderMeasurableEquivOfOrder horder).symm ts) := by sorry
