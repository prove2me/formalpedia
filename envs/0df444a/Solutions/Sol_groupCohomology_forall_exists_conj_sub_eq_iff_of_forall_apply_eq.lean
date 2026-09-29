-- Prove2me | solution 1 for groupCohomology.forall_exists_conj_sub_eq_iff_of_forall_apply_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/0e8e7fa5-35ae-559a-b5f7-86bc0824e6a9

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_forall_exists_conj_sub_eq_iff_of_forall_apply_eq

set_option autoImplicit false

universe u

open CategoryTheory groupCohomology

theorem solution
    {k G : Type u} [CommRing k] [Group G] (A : Rep.{u} k G) (S : Subgroup G)
    (htriv : ∀ s ∈ S, ∀ v : A, A.ρ s v = v) (c : cocycles₁ (Rep.res S.subtype A)) :
    (∀ g : G, ∃ a : A, ∀ s t : S, (g⁻¹ * s * g : G) = t →
        A.ρ g (c t) - c s = A.ρ (s : G) a - a) ↔
      ∀ (g : G) (s t : S), (g⁻¹ * s * g : G) = t → A.ρ g (c t) = c s := by
  constructor
  · intro h g s t hst
    obtain ⟨a, ha⟩ := h g
    have := ha s t hst
    rwa [htriv _ s.2, sub_self, sub_eq_zero] at this
  · intro h g
    exact ⟨0, fun s t hst => by rw [h g s t hst, sub_self, map_zero, sub_self]⟩

end S_groupCohomology_forall_exists_conj_sub_eq_iff_of_forall_apply_eq
end P2MW
export P2MW.S_groupCohomology_forall_exists_conj_sub_eq_iff_of_forall_apply_eq (solution)
