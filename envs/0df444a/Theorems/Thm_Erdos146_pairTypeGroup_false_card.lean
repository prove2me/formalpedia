-- Prove2me | Theorems.Thm_Erdos146_pairTypeGroup_false_card
-- name    : Erdos146.pairTypeGroup_false_card
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T04:45:07.709997+00:00
-- url     : https://prove2.me/theorems/b3d0ed1e-ad20-41fa-956f-991860aed86c
-- title:
--   Size of the false-valued type group
-- statement:
--   Step in the passage from the two-bit kernel of Section 5 to the array-level entropy functional $E(u,z)$ of Section 7, where the empirical distribution of a coordinate over a parent array replaces a fixed kernel. Cardinality of the group of coordinates whose parent pair has the given type and child bit $0$.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L13318-L13325

import Definitions.Def_erdos146_core2
import Mathlib.AlgebraicTopology.SimplexCategory.Basic

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem Erdos146.pairTypeGroup_false_card
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension) :
    (pairTypeGroup parents coordinate 0).card =
      (parentCount - pairParentCoordinateOneCount parents coordinate).choose 2 := by sorry
