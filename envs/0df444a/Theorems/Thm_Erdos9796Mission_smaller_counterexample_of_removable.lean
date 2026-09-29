-- Prove2me | Theorems.Thm_Erdos9796Mission_smaller_counterexample_of_removable
-- name    : Erdos9796Mission.smaller_counterexample_of_removable
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-12T21:05:42.116718+00:00
-- url     : https://prove2.me/theorems/723031a3-ceea-4c27-8c5d-8f18a141a272
-- title:
--   Deleting a removable vertex gives a smaller counterexample
-- statement:
--   Let A be a finite planar point set in strictly convex position with at least two points. If A has a vertex whose deletion preserves four equidistant witnesses at every remaining vertex, then there exists a nonempty point set with fewer points than A that remains in strictly convex position and retains the four-witness property.
-- source:
--   https://github.com/mysticflounder/erdos-97-96-formalization/blob/743b102037e9c43dd610a4db761433ce35862a99/lean/Erdos9796Proof/P97/SmallerCounterexample.lean#L30-L39

import Definitions.Def_Erdos9796Mission_RemovableVertex

open Erdos9796Mission

theorem Erdos9796Mission.smaller_counterexample_of_removable
    {A : Finset Plane} (hconv : ConvexIndep (A : Set Plane))
    {x : Plane} (hrem : IsRemovableVertex A x) (hcard : 1 < A.card) :
    ∃ B : Finset Plane, B.Nonempty ∧ B.card < A.card ∧
      ConvexIndep (B : Set Plane) ∧ HasNEquidistantProperty 4 B := by sorry
