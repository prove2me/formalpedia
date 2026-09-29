-- Prove2me | Theorems.Thm_Erdos9796Mission_finite_nine_exclusion
-- name    : Erdos9796Mission.finite_nine_exclusion
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-05T22:50:40.088087+00:00
-- url     : https://prove2.me/theorems/e655c70a-0709-4c62-8e4a-e4645fad237b
-- title:
--   Base case: exclude a nine-vertex counterexample
-- statement:
--   For every set $A$ of exactly nine points in strictly convex position in the Euclidean plane, some vertex has no four other vertices at a common positive distance.
--
--   $$|A|=9\quad\Longrightarrow\quad\exists p\in A\;\forall r>0:\;|\{q\in A:\|p-q\|=r\}|\le3.$$
--
--   This is the exact-cardinality base case used by the repository's descent strategy. Its existing proof is separate from the unresolved large-cardinality descent.
-- source:
--   https://github.com/mysticflounder/erdos-97-96-formalization/blob/757d852766f377f7c1a0ffeeef6d3526bc0cb7a4/lean/Erdos9796Proof/P97/N9Endpoint/Closure.lean#L56

/- Statement-only mission draft: SKETCH — NOT PROMOTABLE.
Source and precise status are recorded in items.json. -/
import Definitions.Def_Erdos9796Mission
open Erdos9796Mission

theorem Erdos9796Mission.finite_nine_exclusion :
    ∀ A : Finset Plane, A.card = 9 → ConvexIndep (A : Set Plane) → ¬ HasNEquidistantProperty 4 A := by sorry
