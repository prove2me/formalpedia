-- Prove2me | solution 1 for groupCohomology.locRes_mem_continuousH1_of_mem_continuousH1S
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/71735cbf-d8c2-5f39-bd95-7f7ac2a3d68d

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Theorems.Thm_groupCohomology_locRes_extArithLoc_apply_mem_continuousH1
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_locRes_mem_continuousH1_of_mem_continuousH1S

set_option autoImplicit false
open CategoryTheory Module groupCohomology ExtCitation

theorem solution
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes)
    (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (x : H1 M) (hx : x ∈ continuousH1S S M) (v : extArithIndex S) :
    (locRes (extArithLoc S) M v).hom x ∈ continuousH1 (extArithLoc S v) (Rep.res (extArithLoc S v) M) :=
  groupCohomology.locRes_extArithLoc_apply_mem_continuousH1 S M x (continuousH1S_le_continuousH1 S M hx) v

end S_groupCohomology_locRes_mem_continuousH1_of_mem_continuousH1S
end P2MW
export P2MW.S_groupCohomology_locRes_mem_continuousH1_of_mem_continuousH1S (solution)
