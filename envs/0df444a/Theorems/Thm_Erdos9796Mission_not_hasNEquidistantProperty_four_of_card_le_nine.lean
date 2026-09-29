-- Prove2me | Theorems.Thm_Erdos9796Mission_not_hasNEquidistantProperty_four_of_card_le_nine
-- name    : Erdos9796Mission.not_hasNEquidistantProperty_four_of_card_le_nine
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-12T13:12:35.528092+00:00
-- url     : https://prove2.me/theorems/762cc684-26e4-41c0-8d39-2bf41c78d1a8
-- title:
--   Problem 97 holds through nine points
-- statement:
--   Every nonempty finite planar point set of at most nine points in strictly convex position has a vertex for which no positive-radius circle centered there contains four other points of the set.
-- source:
--   https://github.com/mysticflounder/erdos-97-96-formalization/blob/10136cbd97ce7adae0b7bdb0fa28a67dfde01906/lean/Erdos9796Proof/P97/SmallCardinality.lean#L43-L49

import Theorems.Thm_Erdos9796Mission_counterexample_card_ge_nine
import Theorems.Thm_Erdos9796Mission_finite_nine_exclusion

open Erdos9796Mission

theorem Erdos9796Mission.not_hasNEquidistantProperty_four_of_card_le_nine :
    ∀ A : Finset Plane, A.Nonempty → ConvexIndep (A : Set Plane) →
      A.card ≤ 9 → ¬ HasNEquidistantProperty 4 A := by sorry
