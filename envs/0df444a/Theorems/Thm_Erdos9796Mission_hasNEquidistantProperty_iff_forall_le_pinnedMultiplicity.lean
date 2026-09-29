-- Prove2me | Theorems.Thm_Erdos9796Mission_hasNEquidistantProperty_iff_forall_le_pinnedMultiplicity
-- name    : Erdos9796Mission.hasNEquidistantProperty_iff_forall_le_pinnedMultiplicity
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-11T16:31:49.047954+00:00
-- url     : https://prove2.me/theorems/8a90d80b-991b-45a6-a34f-7be569080670
-- title:
--   The repeated-distance property is a pointwise multiplicity bound
-- statement:
--   For n > 0, the repeated-distance property gives pinned multiplicity at least n at every point of A, and those pointwise bounds give the repeated-distance property.
-- source:
--   https://github.com/mysticflounder/erdos-97-96-formalization/blob/3d0e9306396f0aa6639f4453174693990fe9c242/lean/Erdos9796Proof/P97/PinnedMultiplicity.lean#L219-L228

import Definitions.Def_Erdos9796Mission_PinnedMultiplicity

theorem Erdos9796Mission.hasNEquidistantProperty_iff_forall_le_pinnedMultiplicity
    {A : Finset Erdos9796Mission.Plane} {n : ℕ} (hn : 0 < n) :
    Erdos9796Mission.HasNEquidistantProperty n A ↔
      ∀ p ∈ A, n ≤ Erdos9796Mission.pinnedMultiplicity A p := by sorry
