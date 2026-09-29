-- Prove2me | Theorems.Thm_Erdos9796Mission_not_hasNEquidistantProperty_four_iff_exists_pinnedMultiplicity_le_three
-- name    : Erdos9796Mission.not_hasNEquidistantProperty_four_iff_exists_pinnedMultiplicity_le_three
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-11T16:36:23.392433+00:00
-- url     : https://prove2.me/theorems/19cb2660-eec5-44fe-87af-d7b2de8ab3f5
-- title:
--   Failure of four witnesses means multiplicity at most three
-- statement:
--   If a finite point set fails the four-equidistant-witness property, it has a point whose pinned distance multiplicity is at most three. Conversely, such a point makes the four-witness property fail.
-- source:
--   https://github.com/mysticflounder/erdos-97-96-formalization/blob/3d0e9306396f0aa6639f4453174693990fe9c242/lean/Erdos9796Proof/P97/PinnedMultiplicity.lean#L230-L239

import Definitions.Def_Erdos9796Mission_PinnedMultiplicity

theorem Erdos9796Mission.not_hasNEquidistantProperty_four_iff_exists_pinnedMultiplicity_le_three
    (A : Finset Erdos9796Mission.Plane) :
    ¬ Erdos9796Mission.HasNEquidistantProperty 4 A ↔
      ∃ p ∈ A, Erdos9796Mission.pinnedMultiplicity A p ≤ 3 := by sorry
