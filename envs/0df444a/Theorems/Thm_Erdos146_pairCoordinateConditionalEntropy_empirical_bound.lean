-- Prove2me | Theorems.Thm_Erdos146_pairCoordinateConditionalEntropy_empirical_bound
-- name    : Erdos146.pairCoordinateConditionalEntropy_empirical_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T04:46:23.669799+00:00
-- url     : https://prove2.me/theorems/76961db9-c749-4960-a18e-68e4492f6a79
-- title:
--   Coordinatewise empirical entropy bound
-- statement:
--   Step in the passage from the two-bit kernel of Section 5 to the array-level entropy functional $E(u,z)$ of Section 7, where the empirical distribution of a coordinate over a parent array replaces a fixed kernel. Bound on the conditional entropy contributed by a single coordinate of the parent/child arrays.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L14092-L14144

import Definitions.Def_erdos146_core2
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Real.Basic

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem Erdos146.pairCoordinateConditionalEntropy_empirical_bound
    {parentCount dimension : ℕ}
    (hparents : 4 ≤ parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension) :
    pairCoordinateConditionalEntropy parents children coordinate ≤
      kappa +
        logTwo 3 *
          empiricalAverageDisagreement parentCount
            (pairParentCoordinateOneCount parents coordinate)
            (pairCoordinateKernel (by omega)
              parents children coordinate) +
        (binaryEntropy
            ((pairChildCoordinateOneCount children coordinate : ℝ) /
              (parentCount.choose 2 : ℝ)) -
          binaryEntropy
            ((pairParentCoordinateOneCount parents coordinate : ℝ) /
              (parentCount : ℝ))) / 2 +
        empiricalEntropyError parentCount := by sorry
