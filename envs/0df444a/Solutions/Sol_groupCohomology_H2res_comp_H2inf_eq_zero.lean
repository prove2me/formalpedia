-- Prove2me | solution 1 for groupCohomology.H2res_comp_H2inf_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/65006016-5172-5805-8a56-ac09a95eaec0

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_H2res_comp_H2inf_eq_zero

set_option autoImplicit false

universe u

open CategoryTheory groupCohomology Rep

theorem solution
    {k G : Type u} [CommRing k] [Group G] (A : Rep k G) (S : Subgroup G) [S.Normal] :
    groupCohomology.map (A := A.quotientToInvariants S) (B := A)
        (QuotientGroup.mk' S) (Rep.ofHom (A.ρ.quotientToInvariants_lift S)) 2 ≫
      groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype A)) 2 = 0 := by
  ext x
  induction x using H2_induction_on with | h β =>
  change (groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype A)) 2).hom
    ((groupCohomology.map (QuotientGroup.mk' S) (Rep.ofHom (A.ρ.quotientToInvariants_lift S)) 2).hom
      (H2π _ β)) = 0
  rw [H2π_comp_map_apply, H2π_comp_map_apply, H2π_eq_zero_iff]

  refine ⟨fun _ => (↑(β (1, 1)) : A), funext fun p => ?_⟩
  obtain ⟨s, t⟩ := p
  rw [d₁₂_hom_apply]
  change A.ρ (s : G) (↑(β (1, 1))) - ↑(β (1, 1)) + ↑(β (1, 1))
    = (↑(β (((s : G) : G ⧸ S), ((t : G) : G ⧸ S))) : A)
  rw [show ((s : G) : G ⧸ S) = 1 from (QuotientGroup.eq_one_iff _).2 s.2,
    show ((t : G) : G ⧸ S) = 1 from (QuotientGroup.eq_one_iff _).2 t.2, sub_add_cancel]
  exact (β (1, 1)).2 s

end S_groupCohomology_H2res_comp_H2inf_eq_zero
end P2MW
export P2MW.S_groupCohomology_H2res_comp_H2inf_eq_zero (solution)
