-- Prove2me | solution 1 for groupCohomology.preimageFun_comp_d12_sub_deltaCochain1_mem_levelCoboundaries2
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/4ae963d9-1a11-5188-8bb6-6b04e9acc023

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_ContinuousH2Map
import Definitions.Def_GroupCohomology_ContinuousH1
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_preimageFun_comp_d12_sub_deltaCochain1_mem_levelCoboundaries2

set_option autoImplicit false

universe u

open CategoryTheory

namespace P2mS26U6b
open groupCohomology

variable {k G : Type u} [CommRing k] [Group G]
  {r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)} {A B C : Rep.{u} k G} (φ : A ⟶ B) (ψ : B ⟶ C)

theorem isLevelConstant₁_d₀₁ {m : B}
    (hm : ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s, r s ∈ F.fixingSubgroup → B.ρ s m = m) :
    IsLevelConstant₁ r ((d₀₁ B).hom m) := by
  obtain ⟨F, hF, h⟩ := hm
  refine ⟨F, hF, fun g s hs => ?_⟩
  rw [d₀₁_hom_apply, d₀₁_hom_apply, map_mul, Module.End.mul_apply, h s hs]

theorem lc_sub₁ {X : Type*} [AddGroup X] {f f' : G → X} (hf : IsLevelConstant₁ r f) (hf' : IsLevelConstant₁ r f') :
    IsLevelConstant₁ r (f - f') := by
  obtain ⟨F, hF, h⟩ := hf
  obtain ⟨F', hF', h'⟩ := hf'
  haveI := hF; haveI := hF'
  refine ⟨F ⊔ F', inferInstance, fun g s hs => ?_⟩
  simp only [Pi.sub_apply]
  rw [h g s (IntermediateField.fixingSubgroup_antitone le_sup_left hs),
    h' g s (IntermediateField.fixingSubgroup_antitone le_sup_right hs)]

theorem lc_sub₂ {X : Type*} [AddGroup X] {f f' : G × G → X} (hf : IsLevelConstant₂ r f) (hf' : IsLevelConstant₂ r f') :
    IsLevelConstant₂ r (f - f') := by
  obtain ⟨F, hF, h⟩ := hf
  obtain ⟨F', hF', h'⟩ := hf'
  haveI := hF; haveI := hF'
  refine ⟨F ⊔ F', inferInstance, fun g g' s s' hs hs' => ?_⟩
  simp only [Pi.sub_apply]
  rw [h g g' s s' (IntermediateField.fixingSubgroup_antitone le_sup_left hs)
      (IntermediateField.fixingSubgroup_antitone le_sup_left hs'),
    h' g g' s s' (IntermediateField.fixingSubgroup_antitone le_sup_right hs)
      (IntermediateField.fixingSubgroup_antitone le_sup_right hs')]

theorem d₁₂_comp (e : G → A) : (d₁₂ B).hom (φ.hom ∘ e) = φ.hom ∘ (d₁₂ A).hom e := by
  funext ⟨g, h⟩
  simp only [d₁₂_hom_apply, Function.comp_apply, map_add, map_sub, Rep.hom_comm_apply]

theorem d₂₃_comp (e : G × G → A) : (d₂₃ B).hom (φ.hom ∘ e) = φ.hom ∘ (d₂₃ A).hom e := by
  funext ⟨g, h, j⟩
  simp only [d₂₃_hom_apply, Function.comp_apply, map_add, map_sub, Rep.hom_comm_apply]

theorem d₁₂_d₀₁ (m : B) : (d₁₂ B).hom ((d₀₁ B).hom m) = 0 :=
  LinearMap.mem_ker.1 (coboundaries₁_le_cocycles₁ B ⟨m, rfl⟩)

theorem d₂₃_d₁₂ (y : G → B) : (d₂₃ B).hom ((d₁₂ B).hom y) = 0 :=
  LinearMap.mem_ker.1 (coboundaries₂_le_cocycles₂ B ⟨y, rfl⟩)

theorem d₁₂_cocycles₁ (b : cocycles₁ B) : (d₁₂ B).hom b = 0 := LinearMap.mem_ker.1 b.2

theorem d₂₃_cocycles₂ {b : G × G → B} (hb : b ∈ cocycles₂ B) : (d₂₃ B).hom b = 0 := LinearMap.mem_ker.1 hb

theorem isLevelConstant₁_preimageFun_comp {y : G → B} (hy : IsLevelConstant₁ r y) :
    IsLevelConstant₁ r (preimageFun φ ∘ y) := hy.comp _

theorem isLevelConstant₂_preimageFun_comp {y : G × G → B} (hy : IsLevelConstant₂ r y) :
    IsLevelConstant₂ r (preimageFun φ ∘ y) := hy.comp _

end P2mS26U6b

open P2mS26U6b groupCohomology in
theorem solution {k G : Type u} [CommRing k] [Group G]
    (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) {A B C : Rep.{u} k G} (φ : A ⟶ B) (ψ : B ⟶ C)
    (hφ : Function.Injective φ.hom) (hψ : Function.Surjective ψ.hom) (hex : ∀ b : B, ψ.hom b = 0 ↔ ∃ a : A, φ.hom a = b)
    (c : groupCohomology.cocycles₁ C) (hc : groupCohomology.IsLevelConstant₁ r c)
    (L : G → B) (hL : groupCohomology.IsLevelConstant₁ r L) (hLc : ∀ g, ψ.hom (L g) = c g) :
    (groupCohomology.preimageFun φ ∘ (groupCohomology.d₁₂ B).hom L - groupCohomology.deltaCochain₁ φ ψ hψ c)
      ∈ groupCohomology.levelCoboundaries₂ r A := by
  have hσ : ∀ x : C, ψ.hom (Function.surjInv hψ x) = x := Function.surjInv_eq hψ

  have hkerL : ∀ p, ψ.hom ((d₁₂ B).hom L p) = 0 := by
    rintro ⟨g, h⟩
    rw [d₁₂_hom_apply, map_add, map_sub, Rep.hom_comm_apply, hLc, hLc, hLc,
      (mem_cocycles₁_iff (c : G → C)).1 c.2 g h]
    abel
  have hkerσ : ∀ p, ψ.hom ((d₁₂ B).hom (Function.surjInv hψ ∘ c) p) = 0 := by
    rintro ⟨g, h⟩
    rw [d₁₂_hom_apply, map_add, map_sub, Rep.hom_comm_apply, Function.comp_apply, Function.comp_apply,
      Function.comp_apply, hσ, hσ, hσ, (mem_cocycles₁_iff (c : G → C)).1 c.2 g h]
    abel
  have hφL : ∀ p, φ.hom (preimageFun φ ((d₁₂ B).hom L p)) = (d₁₂ B).hom L p := fun p =>
    apply_preimageFun φ ((hex _).1 (hkerL p))
  have hφδ : ∀ p, φ.hom (deltaCochain₁ φ ψ hψ c p) = (d₁₂ B).hom (Function.surjInv hψ ∘ c) p := fun p =>
    apply_preimageFun φ ((hex _).1 (hkerσ p))

  set e : G → A := preimageFun φ ∘ (L - Function.surjInv hψ ∘ c)
  have he : ∀ g, φ.hom (e g) = L g - Function.surjInv hψ (c g) := fun g =>
    apply_preimageFun φ ((hex _).1 (by rw [Pi.sub_apply, map_sub, hLc, Function.comp_apply, hσ, sub_self]))
  have he' : φ.hom ∘ e = L - Function.surjInv hψ ∘ c := funext he
  have he_lc : IsLevelConstant₁ r e := (lc_sub₁ hL (hc.comp _)).comp _
  refine (mem_levelCoboundaries₂_iff r A _).2 ⟨e, he_lc, funext fun p => hφ ?_⟩
  rw [show φ.hom ((d₁₂ A).hom e p) = (d₁₂ B).hom (φ.hom ∘ e) p by rw [d₁₂_comp]; rfl, he', map_sub,
    Pi.sub_apply, Pi.sub_apply, map_sub, Function.comp_apply, hφL, hφδ]

end S_groupCohomology_preimageFun_comp_d12_sub_deltaCochain1_mem_levelCoboundaries2
end P2MW
export P2MW.S_groupCohomology_preimageFun_comp_d12_sub_deltaCochain1_mem_levelCoboundaries2 (solution)
