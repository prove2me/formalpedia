-- Prove2me | Theorems.Thm_Erdos9796Mission_linear_bound_of_problem97
-- name    : Erdos9796Mission.linear_bound_of_problem97
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-05T22:52:01.285977+00:00
-- url     : https://prove2.me/theorems/d76e105d-be12-48ae-8965-782674afd985
-- title:
--   The bridge: Problem 97 implies the 3n bound and Problem 96
-- statement:
--   Assume the affirmative statement of Erdős Problem 97 for every nonempty finite convex-independent point set in the Euclidean plane. Then every finite convex-independent set $A$, including the empty set, satisfies
--
--   $$u(A)\le3|A|,$$
--
--   and the extremal function satisfies
--
--   $$U_c(n)=O(n).$$
--
--   Here $u(A)$ counts unordered pairs of distinct points at distance one, each pair once, and $U_c(n)$ is the supremum of these counts over convex-independent n-point sets. Both conclusions are required. This is a conditional theorem, with Problem 97 as an explicit hypothesis. The repository records the conditional peeling proof and the subsequent supremum-to-Big-O step; transferring both makes the complete link between the two mission targets reusable.
-- source:
--   https://github.com/mysticflounder/erdos-97-96-formalization/blob/757d852766f377f7c1a0ffeeef6d3526bc0cb7a4/lean/Erdos9796Proof/P96/EuclideanPeeling.lean; https://github.com/mysticflounder/erdos-97-96-formalization/blob/757d852766f377f7c1a0ffeeef6d3526bc0cb7a4/lean/Erdos9796Proof/P96/UpstreamBridge.lean

/- Statement-only mission draft: SKETCH — NOT PROMOTABLE.
Source and precise status are recorded in items.json. -/
import Definitions.Def_Erdos9796Mission
open Erdos9796Mission

theorem Erdos9796Mission.linear_bound_of_problem97 :
    Problem97 → (∀ A : Finset Plane, ConvexIndep (A : Set Plane) → unitDistancePairsCount A ≤ 3 * A.card) ∧ Problem96 := by sorry
