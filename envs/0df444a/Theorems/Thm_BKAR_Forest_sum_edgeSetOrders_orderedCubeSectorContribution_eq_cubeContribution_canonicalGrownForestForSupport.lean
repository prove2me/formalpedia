-- Prove2me | Theorems.Thm_BKAR_Forest_sum_edgeSetOrders_orderedCubeSectorContribution_eq_cubeContribution_canonicalGrownForestForSupport
-- name    : BKAR.Forest.sum_edgeSetOrders_orderedCubeSectorContribution_eq_cubeContribution_canonicalGrownForestForSupport
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:02:18.08068+00:00
-- url     : https://prove2.me/theorems/858acea2-db5e-5cec-b9e3-0a88d9ffae45
-- title:
--   Forest: sum edge Set Orders ordered Cube Sector Contribution eq cube Contribution canonical Grown Forest For Support
-- statement:
--   The canonical grown forest over a support folds its support-indexed ordered
--   cube sectors back to its unordered cube contribution.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/CubeFold.lean#L107-L117
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/CubeFold.lean#L107-L117

import Definitions.Def_BKAR_CubePartition_MeasureSmoothness
import Definitions.Def_BKAR_OrderedAssembly_CanonicalSector
import Definitions.Def_BKAR_OrderedAssembly_CubeFold
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.sum_edgeSetOrders_orderedCubeSectorContribution_eq_cubeContribution_canonicalGrownForestForSupport
    (choices : ActiveExtensionChoice V) (I : ForestIndex V)
    (ρ : (Edge V → ℝ) → ℝ) (hρ : BKARContDiff ρ) :
    Finset.sum (edgeSetOrders I.edges)
      (fun order =>
        (canonicalGrownForestForSupport choices I).orderedCubeSectorContribution
          order ρ) =
      (canonicalGrownForestForSupport choices I).cubeContribution ρ := by sorry
