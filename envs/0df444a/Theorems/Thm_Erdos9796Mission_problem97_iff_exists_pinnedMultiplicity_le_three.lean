-- Prove2me | Theorems.Thm_Erdos9796Mission_problem97_iff_exists_pinnedMultiplicity_le_three
-- name    : Erdos9796Mission.problem97_iff_exists_pinnedMultiplicity_le_three
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-11T16:41:32.826257+00:00
-- url     : https://prove2.me/theorems/b7e1bd91-c3a4-4b5d-b8b0-62475ed73659
-- title:
--   Problem 97 and its pinned multiplicity formulation
-- statement:
--   Problem 97 implies that every nonempty finite planar point set in strictly convex position contains a point whose pinned distance multiplicity is at most three. The converse implication also holds. These two implications restate the open problem without proving it.
-- source:
--   https://github.com/mysticflounder/erdos-97-96-formalization/blob/3d0e9306396f0aa6639f4453174693990fe9c242/lean/Erdos9796Proof/P97/PinnedMultiplicity.lean#L241-L262

import Definitions.Def_Erdos9796Mission_PinnedMultiplicity

theorem Erdos9796Mission.problem97_iff_exists_pinnedMultiplicity_le_three :
    Erdos9796Mission.Problem97 ↔
      ∀ A : Finset Erdos9796Mission.Plane,
        A.Nonempty → Erdos9796Mission.ConvexIndep (A : Set Erdos9796Mission.Plane) →
          ∃ p ∈ A, Erdos9796Mission.pinnedMultiplicity A p ≤ 3 := by sorry
