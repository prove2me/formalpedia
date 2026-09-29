-- Prove2me | solution 1 for groupCohomology.Cores.map_cores_eq_cores_map
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/24fb0277-0086-5d98-b66e-9717bcc17011

import Mathlib
import Definitions.Def_GroupCohomology_Corestriction2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_Cores_map_cores_eq_cores_map

set_option autoImplicit false
p2m_open "CategoryTheory groupCohomology P2MW.S_groupCohomology_Cores_map_cores_eq_cores_map.groupCohomology"

namespace groupCohomology
p2m_export "groupCohomology" "congr H2π_comp_map_apply map H2_induction_on Cores.Transversal Cores.fintypeQuot Cores.cores Cores.cores_H2π"
namespace Cores
p2m_export "groupCohomology.Cores" "Transversal fintypeQuot cor₂ cor₂_apply cores cores_H2π"
namespace Nat
p2m_open "groupCohomology.Cores groupCohomology"

attribute [local instance] groupCohomology.Cores.fintypeQuot

variable {k G : Type} [CommRing k] [Group G] (A B : Rep.{0} k G) (φ : A ⟶ B) {K : Subgroup G} [K.FiniteIndex] (τ : Transversal K)

theorem cor₂_comp (u : K × K → A) : cor₂ B τ (fun x => φ.hom (u x)) = fun gg => φ.hom (cor₂ A τ u gg) := by
  funext gg
  obtain ⟨g₁, g₂⟩ := gg
  rw [cor₂_apply, cor₂_apply, map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Rep.hom_comm_apply]

theorem main (z : groupCohomology (Rep.res K.subtype A) 2) :
    (groupCohomology.map (MonoidHom.id G) φ 2).hom (Cores.cores A τ z) =
      Cores.cores B τ ((groupCohomology.map (A := Rep.res K.subtype A) (B := Rep.res K.subtype B)
        (MonoidHom.id ↥K) ((Rep.resFunctor K.subtype).map φ) 2).hom z) := by
  induction z using H2_induction_on with
  | h u =>
    rw [Cores.cores_H2π, groupCohomology.H2π_comp_map_apply, groupCohomology.H2π_comp_map_apply, Cores.cores_H2π]
    congr 1
    apply Subtype.ext
    change (fun gg => φ.hom (cor₂ A τ u gg)) = cor₂ B τ (fun x => φ.hom (u x))
    rw [cor₂_comp]

end groupCohomology.Cores.Nat

theorem solution
    {k G : Type} [CommRing k] [Group G] (A B : Rep.{0} k G) (φ : A ⟶ B)
    (K : Subgroup G) [K.FiniteIndex] (τ : Cores.Transversal K) (z : groupCohomology (Rep.res K.subtype A) 2) :
    (groupCohomology.map (MonoidHom.id G) φ 2).hom (Cores.cores A τ z) =
      Cores.cores B τ ((groupCohomology.map (MonoidHom.id ↥K) ((Rep.resFunctor K.subtype).map φ) 2).hom z) :=
  groupCohomology.Cores.Nat.main A B φ τ z

end S_groupCohomology_Cores_map_cores_eq_cores_map
end P2MW
export P2MW.S_groupCohomology_Cores_map_cores_eq_cores_map (solution)
