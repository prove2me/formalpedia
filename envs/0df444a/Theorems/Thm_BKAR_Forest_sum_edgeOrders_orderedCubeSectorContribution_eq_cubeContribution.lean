-- Prove2me | Theorems.Thm_BKAR_Forest_sum_edgeOrders_orderedCubeSectorContribution_eq_cubeContribution
-- name    : BKAR.Forest.sum_edgeOrders_orderedCubeSectorContribution_eq_cubeContribution
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:01:56.300038+00:00
-- url     : https://prove2.me/theorems/5cdad109-c2e9-5df5-98de-aef0f8289a18
-- title:
--   Forest: sum edge Orders ordered Cube Sector Contribution eq cube Contribution
-- statement:
--   The existing cube-partition theorem, folded in the direction needed by
--   support-indexed ordered assembly.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/CubeFold.lean#L49-L55
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/CubeFold.lean#L49-L55

import Definitions.Def_BKAR_CubePartition_MeasureSmoothness
import Definitions.Def_BKAR_OrderedAssembly_CanonicalSector
import Definitions.Def_BKAR_OrderedAssembly_CubeFold
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.sum_edgeOrders_orderedCubeSectorContribution_eq_cubeContribution
    (F : Forest V) (ρ : (Edge V → ℝ) → ℝ)
    (hρ : BKARContDiff ρ) :
    Finset.sum F.edgeOrders
      (fun order => F.orderedCubeSectorContribution order ρ) =
      F.cubeContribution ρ := by sorry
