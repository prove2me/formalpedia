-- Prove2me | Theorems.Thm_Erdos9796Mission_counterexample_card_ge_ten
-- name    : Erdos9796Mission.counterexample_card_ge_ten
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-12T13:03:22.086499+00:00
-- url     : https://prove2.me/theorems/e1b3299f-23b0-45b2-8d9a-4c28b2de049e
-- title:
--   Every counterexample has at least ten points
-- statement:
--   Every nonempty finite planar point set in strictly convex position such that, at each vertex, four other points lie at some common positive distance from that vertex has at least ten points. The radius may depend on the vertex.
-- source:
--   https://github.com/mysticflounder/erdos-97-96-formalization/blob/10136cbd97ce7adae0b7bdb0fa28a67dfde01906/lean/Erdos9796Proof/P97/SmallCardinality.lean#L31-L38

import Theorems.Thm_Erdos9796Mission_counterexample_card_ge_nine
import Theorems.Thm_Erdos9796Mission_finite_nine_exclusion

open Erdos9796Mission

theorem Erdos9796Mission.counterexample_card_ge_ten :
    ∀ A : Finset Plane, A.Nonempty → ConvexIndep (A : Set Plane) →
      HasNEquidistantProperty 4 A → 10 ≤ A.card := by sorry
