-- Prove2me | solution 1 for groupCohomology.finite_H1_of_shortExact
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/d0dc434e-4034-5c6d-ab59-bd6364bbb5b4

import Mathlib
import Theorems.Thm_groupCohomology_finite_groupCohomology_of_shortExact
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_finite_H1_of_shortExact

set_option autoImplicit false

universe u

open CategoryTheory groupCohomology
open Rep.FiniteCyclicGroup

theorem solution
    {k G : Type u} [CommRing k] [Group G] {X : ShortComplex (Rep k G)} (hX : X.ShortExact)
    [Finite (H1 X.X₁)] [Finite (H1 X.X₃)] :
    Finite (H1 X.X₂) := by
  exact finite_groupCohomology_of_shortExact hX 1

end S_groupCohomology_finite_H1_of_shortExact
end P2MW
export P2MW.S_groupCohomology_finite_H1_of_shortExact (solution)
