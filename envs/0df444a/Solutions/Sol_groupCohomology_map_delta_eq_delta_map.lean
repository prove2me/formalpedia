-- Prove2me | solution 1 for groupCohomology.map_delta_eq_delta_map
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/93345db0-1123-5ebb-a54c-2b3888429a71

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_map_delta_eq_delta_map

set_option autoImplicit false
p2m_open "CategoryTheory groupCohomology P2MW.S_groupCohomology_map_delta_eq_delta_map.groupCohomology"

namespace groupCohomology
p2m_export "groupCohomology" "cochainsFunctor cochainsMap cochainsMap_comp map π δ map_cochainsFunctor_shortExact"
namespace InfLes
p2m_open "groupCohomology"

variable {k G G' : Type} [CommRing k] [Group G] [Group G'] (π : G' →* G)

lemma cochainsMap_square {A B : Rep k G} {A' B' : Rep k G'} (f : A ⟶ B) (f' : A' ⟶ B')
    (φ : Rep.res π A ⟶ A') (ψ : Rep.res π B ⟶ B') (w : (Rep.resFunctor π).map f ≫ ψ = φ ≫ f') :
    (cochainsFunctor k G).map f ≫ cochainsMap π ψ = cochainsMap π φ ≫ (cochainsFunctor k G').map f' := by
  have h₁ : cochainsMap ((MonoidHom.id G).comp π) ((Rep.resFunctor π).map f ≫ ψ) =
      (cochainsFunctor k G).map f ≫ cochainsMap π ψ := cochainsMap_comp (MonoidHom.id G) π f ψ
  have h₂ : cochainsMap (π.comp (MonoidHom.id G')) ((Rep.resFunctor (MonoidHom.id G')).map φ ≫ f') =
      cochainsMap π φ ≫ (cochainsFunctor k G').map f' := cochainsMap_comp π (MonoidHom.id G') φ f'
  rw [← h₁, ← h₂, w]
  rfl

private noncomputable def _root_.groupCohomology.InfLes.hom {X : ShortComplex (Rep k G)} {X' : ShortComplex (Rep k G')}
    (φ₁ : Rep.res π X.X₁ ⟶ X'.X₁) (φ₂ : Rep.res π X.X₂ ⟶ X'.X₂) (φ₃ : Rep.res π X.X₃ ⟶ X'.X₃)
    (w₁ : (Rep.resFunctor π).map X.f ≫ φ₂ = φ₁ ≫ X'.f) (w₂ : (Rep.resFunctor π).map X.g ≫ φ₃ = φ₂ ≫ X'.g) :
    X.map (cochainsFunctor k G) ⟶ X'.map (cochainsFunctor k G') where
  τ₁ := cochainsMap π φ₁
  τ₂ := cochainsMap π φ₂
  τ₃ := cochainsMap π φ₃
  comm₁₂ := (cochainsMap_square π X.f X'.f φ₁ φ₂ w₁).symm
  comm₂₃ := (cochainsMap_square π X.g X'.g φ₂ φ₃ w₂).symm

p2m_export "groupCohomology.InfLes" "hom"
end groupCohomology.InfLes

open CategoryTheory _root_.groupCohomology _root_.P2MW.S_groupCohomology_map_delta_eq_delta_map.groupCohomology in

theorem solution
    {k G G' : Type} [CommRing k] [Group G] [Group G'] (π : G' →* G)
    {X : ShortComplex (Rep k G)} (hX : X.ShortExact) {X' : ShortComplex (Rep k G')} (hX' : X'.ShortExact)
    (φ₁ : Rep.res π X.X₁ ⟶ X'.X₁) (φ₂ : Rep.res π X.X₂ ⟶ X'.X₂) (φ₃ : Rep.res π X.X₃ ⟶ X'.X₃)
    (w₁ : (Rep.resFunctor π).map X.f ≫ φ₂ = φ₁ ≫ X'.f) (w₂ : (Rep.resFunctor π).map X.g ≫ φ₃ = φ₂ ≫ X'.g)
    (i j : ℕ) (hij : i + 1 = j) (y : groupCohomology X.X₃ i) :
    (groupCohomology.map π φ₁ j).hom ((groupCohomology.δ hX i j hij).hom y) =
      (groupCohomology.δ hX' i j hij).hom ((groupCohomology.map π φ₃ i).hom y) := by
  have h := HomologicalComplex.HomologySequence.δ_naturality (groupCohomology.InfLes.hom π φ₁ φ₂ φ₃ w₁ w₂)
    (map_cochainsFunctor_shortExact hX) (map_cochainsFunctor_shortExact hX') i j hij
  exact congrArg (fun F => F.hom y) h

end S_groupCohomology_map_delta_eq_delta_map
end P2MW
export P2MW.S_groupCohomology_map_delta_eq_delta_map (solution)
