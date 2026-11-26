-- Prove2me | Theorems.Thm_BKAR_Forest_orderedContribution_eq_orderedCubeSectorContribution_of_contDiff
-- name    : BKAR.Forest.orderedContribution_eq_orderedCubeSectorContribution_of_contDiff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:13:07.048482+00:00
-- url     : https://prove2.me/theorems/a8ee7e3d-f828-4e91-b927-a4b38bd16dc1
-- title:
--   Forest: ordered Contribution eq ordered Cube Sector Contribution of cont Diff
-- statement:
--   Arbitrary finite-order simplex-sector conversion: under the global BKAR
--   smoothness hypothesis,
--   the recursive ordered contribution equals the corresponding closed ordered
--   cube-sector contribution.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Finite.lean#L754-L782
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Finite.lean#L754-L782

import Definitions.Def_BKAR_CubePartition_SimplexSector
import Definitions.Def_BKAR_CubePartition_SimplexSector_Finite
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.orderedContribution_eq_orderedCubeSectorContribution_of_contDiff
    (F : Forest V) {order : List (Edge V)} (horder : order ∈ F.edgeOrders)
    (ρ : (Edge V → ℝ) → ℝ) (hρ : BKARContDiff ρ) :
    F.orderedContribution order ρ =
      F.orderedCubeSectorContribution order ρ := by sorry
