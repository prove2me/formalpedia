-- Prove2me | solution 1 for groupCohomology.finrank_inflationImage_eq_finrank_H1_quotientToInvariants
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/5fce5ff4-e50c-53cd-a9f3-66e30701e04c

import Mathlib
import Definitions.Def_GroupCohomology_LocallyConstantClasses
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_finrank_inflationImage_eq_finrank_H1_quotientToInvariants

open CategoryTheory Module groupCohomology

universe u

theorem solution {k G : Type u} [Field k] [Group G] (A : Rep k G) (S : Subgroup G) [S.Normal] :
    finrank k (inflationImage A S) = finrank k (H1 (A.quotientToInvariants S)) :=
  LinearMap.finrank_range_of_inj
    ((ModuleCat.mono_iff_injective _).1 (inferInstance : Mono (H1InfRes A S).f))

end S_groupCohomology_finrank_inflationImage_eq_finrank_H1_quotientToInvariants
end P2MW
export P2MW.S_groupCohomology_finrank_inflationImage_eq_finrank_H1_quotientToInvariants (solution)
