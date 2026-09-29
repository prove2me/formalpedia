-- Prove2me | solution 1 for groupCohomology.Kummer.natCard_H1_eq_natCard_quotient
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/9fc669a9-a01c-563d-a8ba-ee8462e69307

import Mathlib
import Definitions.Def_GroupCohomology_Kummer
import Theorems.Thm_groupCohomology_Kummer_ker_kummerHom
import Theorems.Thm_groupCohomology_Kummer_kummerHom_surjective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_Kummer_natCard_H1_eq_natCard_quotient

set_option autoImplicit false

universe u v

open groupCohomology groupCohomology.Kummer

theorem solution
    {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (p : ℕ) :
    Nat.card (H1 (kummerRep K L p))
      = Nat.card (powerSubgroup K L p ⧸
          ((powMonoidHom p : Kˣ →* Kˣ).range).subgroupOf (powerSubgroup K L p)) := by

  let e : (powerSubgroup K L p ⧸
        ((powMonoidHom p : Kˣ →* Kˣ).range).subgroupOf (powerSubgroup K L p))
      ≃* Multiplicative (H1 (kummerRep K L p)) :=
    (QuotientGroup.quotientMulEquivOfEq (ker_kummerHom (K := K) (L := L) p).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ (kummerHom_surjective p))
  exact ((Nat.card_congr e.toEquiv).trans (Nat.card_congr Multiplicative.toAdd)).symm

end S_groupCohomology_Kummer_natCard_H1_eq_natCard_quotient
end P2MW
export P2MW.S_groupCohomology_Kummer_natCard_H1_eq_natCard_quotient (solution)
