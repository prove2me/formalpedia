-- Prove2me | solution 1 for groupCohomology.continuousH2SrInflation_H2pi_eq_of_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/a810e531-fade-577d-a8a9-3ae9c7344971

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_LevelSubgroup
import Definitions.Def_GroupCohomology_ContinuousH2Inflation
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelInflation
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_continuousH2SrInflation_H2pi_eq_of_le

set_option autoImplicit false
open CategoryTheory groupCohomology

theorem solution
    {k G : Type} [CommRing k] [Group G] (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (S : Finset Nat.Primes) (M : Rep.{0} k G)
    (F F' : IntermediateField ℚ (AlgebraicClosure ℚ)) (hF : F.IsUnramifiedOutside S) (hF' : F'.IsUnramifiedOutside S) [Normal ℚ F] [Normal ℚ F']
    (f : cocycles₂ (M.quotientToInvariants (F.fixingSubgroup.comap r))) (f' : cocycles₂ (M.quotientToInvariants (F'.fixingSubgroup.comap r)))
    (hff' : ∀ g h : G, ((f' ((g : G ⧸ F'.fixingSubgroup.comap r), (h : G ⧸ F'.fixingSubgroup.comap r)) : M.quotientToInvariants _) : M)
      = ((f ((g : G ⧸ F.fixingSubgroup.comap r), (h : G ⧸ F.fixingSubgroup.comap r)) : M.quotientToInvariants _) : M)) :
    continuousH2SrInflation r S M F' hF' (H2π _ f') = continuousH2SrInflation r S M F hF (H2π _ f) := by
  rw [continuousH2SrInflation_H2π, continuousH2SrInflation_H2π]
  congr 1
  apply Subtype.ext
  funext gh
  obtain ⟨g, h⟩ := gh
  exact hff' g h

end S_groupCohomology_continuousH2SrInflation_H2pi_eq_of_le
end P2MW
export P2MW.S_groupCohomology_continuousH2SrInflation_H2pi_eq_of_le (solution)
