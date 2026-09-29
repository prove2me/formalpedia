-- Prove2me | solution 1 for groupCohomology.Kummer.ker_kummerHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/a671362c-a9cc-57c4-8dba-1ddfb07218e9

import Mathlib
import Definitions.Def_GroupCohomology_Kummer
import Theorems.Thm_groupCohomology_Kummer_kummerClass_eq_zero_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_Kummer_ker_kummerHom

set_option autoImplicit false

universe u v

open groupCohomology groupCohomology.Kummer

theorem solution
    {K L : Type} [Field K] [Field L] [Algebra K L] [IsGalois K L] (p : ℕ) :
    (kummerHom K L p).ker
      = ((powMonoidHom p : Kˣ →* Kˣ).range).subgroupOf (powerSubgroup K L p) := by
  ext a
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, kummerHom_apply, ofAdd_eq_one,
    kummerClass_eq_zero_iff]
  exact ⟨fun ⟨b, hb⟩ => ⟨b, hb⟩, fun ⟨b, hb⟩ => ⟨b, hb⟩⟩

end S_groupCohomology_Kummer_ker_kummerHom
end P2MW
export P2MW.S_groupCohomology_Kummer_ker_kummerHom (solution)
