-- Prove2me | Theorems.Thm_Erdos9796Mission_hasNEquidistantPointsAt_iff_le_pinnedMultiplicity
-- name    : Erdos9796Mission.hasNEquidistantPointsAt_iff_le_pinnedMultiplicity
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-11T16:29:48.409758+00:00
-- url     : https://prove2.me/theorems/50911e98-2b92-48f9-82e1-ebbe15ee4ef8
-- title:
--   Equidistant witnesses are a pinned-multiplicity lower bound
-- statement:
--   For n > 0, a positive radius containing at least n points gives pinned distance multiplicity at least n; conversely, that multiplicity bound supplies a positive radius containing at least n points.
-- source:
--   https://github.com/mysticflounder/erdos-97-96-formalization/blob/3d0e9306396f0aa6639f4453174693990fe9c242/lean/Erdos9796Proof/P97/PinnedMultiplicity.lean#L173-L199

import Definitions.Def_Erdos9796Mission_PinnedMultiplicity

theorem Erdos9796Mission.hasNEquidistantPointsAt_iff_le_pinnedMultiplicity
    {A : Finset Erdos9796Mission.Plane} {p : Erdos9796Mission.Plane} {n : ℕ}
    (hn : 0 < n) :
    Erdos9796Mission.HasNEquidistantPointsAt n A p ↔
      n ≤ Erdos9796Mission.pinnedMultiplicity A p := by sorry
