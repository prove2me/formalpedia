-- Prove2me | solution 1 for groupCohomology.bijective_map_top_subtype
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/596b5f42-75fa-505d-b521-fceeb2368f6e

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_bijective_map_top_subtype

set_option autoImplicit false
open CategoryTheory groupCohomology

set_option maxHeartbeats 3200000 in

theorem solution {k G : Type} [CommRing k] [Group G] (A : Rep k G) (n : ℕ) :
    Function.Bijective (groupCohomology.map (⊤ : Subgroup G).subtype (𝟙 (Rep.res (⊤ : Subgroup G).subtype A)) n).hom := by
  classical
  set T : Subgroup G := ⊤ with hT
  haveI hlev : ∀ i, IsIso ((cochainsMap T.subtype (𝟙 (Rep.res T.subtype A))).f i) := by
    intro i
    rw [cochainsMap_f]
    apply (ConcreteCategory.isIso_iff_bijective _).2
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.coe_comp]
    refine Function.Bijective.comp ?_ ?_
    ·
      refine ⟨fun v w h => ?_, fun u => ⟨u, rfl⟩⟩
      exact h
    ·
      refine ⟨fun v w h => ?_, fun u => ?_⟩
      · funext z
        have := congrFun h (fun j => ⟨z j, by rw [hT]; trivial⟩)
        simp [LinearMap.funLeft_apply] at this
        exact this
      · refine ⟨fun z => u (fun j => ⟨z j, by rw [hT]; trivial⟩), ?_⟩
        funext y
        simp only [LinearMap.funLeft_apply, Function.comp_def, Subgroup.coe_subtype, Subtype.coe_eta]
  haveI : IsIso (cochainsMap T.subtype (𝟙 (Rep.res T.subtype A))) := HomologicalComplex.Hom.isIso_of_components _
  haveI : IsIso (HomologicalComplex.homologyMap (cochainsMap T.subtype (𝟙 (Rep.res T.subtype A))) n) := inferInstance
  exact ConcreteCategory.bijective_of_isIso (HomologicalComplex.homologyMap (cochainsMap T.subtype (𝟙 (Rep.res T.subtype A))) n)

end S_groupCohomology_bijective_map_top_subtype
end P2MW
export P2MW.S_groupCohomology_bijective_map_top_subtype (solution)
