-- Prove2me | solution 1 for groupCohomology.inhomogeneousCochains_d_d_apply
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/796597b4-ef84-543f-b3b0-0c6968147587

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_inhomogeneousCochains_d_d_apply

set_option autoImplicit false
open CategoryTheory groupCohomology

theorem solution
    {k G : Type} [CommRing k] [Group G] (A : Rep.{0} k G) (n : ℕ) (y : (Fin n → G) → A) :
    (inhomogeneousCochains.d A (n + 1)).hom ((inhomogeneousCochains.d A n).hom y) = 0 := by
  have h := congrArg (fun T => (ModuleCat.Hom.hom T) y) (inhomogeneousCochains.d_comp_d (A := A) (n := n))
  simpa using h

end S_groupCohomology_inhomogeneousCochains_d_d_apply
end P2MW
export P2MW.S_groupCohomology_inhomogeneousCochains_d_d_apply (solution)
