-- Prove2me | Theorems.Thm_Erdos146_pairCoordinatePairMismatchCount_homogeneous
-- name    : Erdos146.pairCoordinatePairMismatchCount_homogeneous
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T04:46:11.030132+00:00
-- url     : https://prove2.me/theorems/ac72a96f-37d7-43e5-89e5-7abe5735eec4
-- title:
--   Mismatch count on a homogeneous type group
-- statement:
--   Step in the passage from the two-bit kernel of Section 5 to the array-level entropy functional $E(u,z)$ of Section 7, where the empirical distribution of a coordinate over a parent array replaces a fixed kernel. On a homogeneous group of coordinate types the mismatch count takes the stated closed form.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L13744-L13790

import Definitions.Def_erdos146_core2
import Mathlib.AlgebraicTopology.SimplexCategory.Basic

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem Erdos146.pairCoordinatePairMismatchCount_homogeneous
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension)
    (pair : PairLayer parentCount 1)
    (outcome : Bool)
    (hgroup :
      pairCoordinateBitType parents coordinate pair =
        (if outcome then (1 : PairBitType) else 0)) :
    pairCoordinatePairMismatchCount parents children coordinate pair =
      if children pair coordinate = outcome then 0 else 2 := by sorry
