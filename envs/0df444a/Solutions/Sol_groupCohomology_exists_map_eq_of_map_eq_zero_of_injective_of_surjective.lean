-- Prove2me | solution 1 for groupCohomology.exists_map_eq_of_map_eq_zero_of_injective_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/f03171bb-4520-5b99-a92f-bb5754fb5ab9

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_exists_map_eq_of_map_eq_zero_of_injective_of_surjective

set_option autoImplicit false
p2m_open "CategoryTheory groupCohomology P2MW.S_groupCohomology_exists_map_eq_of_map_eq_zero_of_injective_of_surjective.groupCohomology"

namespace groupCohomology
p2m_export "groupCohomology" "mapShortComplex₂_exact map functor π"
namespace LESAux
p2m_open "groupCohomology"

theorem shortExact_of_maps {k G : Type} [CommRing k] [Group G] {X : ShortComplex (Rep k G)}
    (hf : Function.Injective X.f.hom) (hg : Function.Surjective X.g.hom)
    (hfg : ∀ y : X.X₂, X.g.hom y = 0 ↔ y ∈ Set.range X.f.hom) : X.ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ ((Rep.mono_iff_injective _).2 hf) ((Rep.epi_iff_surjective _).2 hg)
  refine Functor.reflects_exact_of_faithful (forget₂ (Rep k G) (ModuleCat k)) _ ?_
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
  intro y
  exact hfg y

end groupCohomology.LESAux

theorem solution
    {k G : Type} [CommRing k] [Group G] {X₁ X₂ X₃ : Rep.{0} k G} (j : X₁ ⟶ X₂) (π : X₂ ⟶ X₃)
    (hj : Function.Injective j.hom) (hπ : Function.Surjective π.hom)
    (hexact : ∀ y : X₂.V, π.hom y = 0 ↔ y ∈ Set.range j.hom)
    (n : ℕ) (y : groupCohomology X₂ n) (hy : (groupCohomology.map (MonoidHom.id G) π n).hom y = 0) :
    ∃ x : groupCohomology X₁ n, (groupCohomology.map (MonoidHom.id G) j n).hom x = y := by
  let X : ShortComplex (Rep k G) := ShortComplex.mk j π (by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro a
    exact (hexact (j.hom a)).2 ⟨a, rfl⟩)
  have hX : X.ShortExact := groupCohomology.LESAux.shortExact_of_maps hj hπ hexact
  have hex := groupCohomology.mapShortComplex₂_exact hX n
  rw [ShortComplex.moduleCat_exact_iff] at hex
  exact hex y hy

end S_groupCohomology_exists_map_eq_of_map_eq_zero_of_injective_of_surjective
end P2MW
export P2MW.S_groupCohomology_exists_map_eq_of_map_eq_zero_of_injective_of_surjective (solution)
