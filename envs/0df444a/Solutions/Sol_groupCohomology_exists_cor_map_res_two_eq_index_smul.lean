-- Prove2me | solution 1 for groupCohomology.exists_cor_map_res_two_eq_index_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/0d8e359f-c8f5-58d9-b67f-c548cebdd62a

import Mathlib
import Definitions.Def_GroupCohomology_Corestriction2
import Theorems.Thm_groupCohomology_Cores_cores_map_res_eq_index_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_exists_cor_map_res_two_eq_index_smul

set_option autoImplicit false
open CategoryTheory groupCohomology

theorem solution
    {k G : Type} [CommRing k] [Group G] (X : Rep k G) (S : Subgroup G) [S.FiniteIndex] :
    ∃ cor : groupCohomology (Rep.res S.subtype X) 2 →ₗ[k] groupCohomology X 2,
      ∀ x : groupCohomology X 2,
        cor ((groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype X)) 2).hom x) = S.index • x := by
  obtain ⟨τ⟩ := (Cores.Transversal.nonempty : Nonempty (Cores.Transversal S))
  exact ⟨Cores.cores X τ, fun x => Cores.cores_map_res_eq_index_smul X S τ x⟩

end S_groupCohomology_exists_cor_map_res_two_eq_index_smul
end P2MW
export P2MW.S_groupCohomology_exists_cor_map_res_two_eq_index_smul (solution)
