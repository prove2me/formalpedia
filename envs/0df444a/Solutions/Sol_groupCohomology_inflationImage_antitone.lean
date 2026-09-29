-- Prove2me | solution 1 for groupCohomology.inflationImage_antitone
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/28fe671b-27b1-57d4-8f8f-f15bc9334b1a

import Mathlib
import Definitions.Def_GroupCohomology_LocallyConstantClasses
import Theorems.Thm_groupCohomology_map_inflationImage_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_inflationImage_antitone

open CategoryTheory Module groupCohomology

universe u

theorem solution {k : Type u} [CommRing k] {G : Type u} [Group G] (M : Rep k G) {S T : Subgroup G} [S.Normal] [T.Normal]
    (hST : S ≤ T) : inflationImage M T ≤ inflationImage M S := by
  have h := map_inflationImage_le (MonoidHom.id G) (𝟙 M) T S
    (by simpa using hST)
  rw [groupCohomology.map_id] at h
  simpa using h

end S_groupCohomology_inflationImage_antitone
end P2MW
export P2MW.S_groupCohomology_inflationImage_antitone (solution)
