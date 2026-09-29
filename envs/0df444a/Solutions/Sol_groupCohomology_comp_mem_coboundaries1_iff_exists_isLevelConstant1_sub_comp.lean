-- Prove2me | solution 1 for groupCohomology.comp_mem_coboundaries1_iff_exists_isLevelConstant1_sub_comp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/c7863ad3-c9c5-54f2-bae5-09a375861ca8

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_ContinuousH2Map
import Definitions.Def_GroupCohomology_ContinuousH1
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_comp_mem_coboundaries1_iff_exists_isLevelConstant1_sub_comp

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
    (hsm : ∀ m : B, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s, r s ∈ F.fixingSubgroup → B.ρ s m = m)
    (b : groupCohomology.cocycles₁ B) (hb : groupCohomology.IsLevelConstant₁ r b) :
    (ψ.hom ∘ b) ∈ groupCohomology.coboundaries₁ C ↔
      ∃ a : groupCohomology.cocycles₁ A, groupCohomology.IsLevelConstant₁ r a ∧
        ((b : G → B) - φ.hom ∘ a) ∈ groupCohomology.coboundaries₁ B := by
  constructor
  · rintro ⟨m, hm⟩
    have hσ : ψ.hom (Function.surjInv hψ m) = m := Function.surjInv_eq hψ m
    set b' : G → B := (b : G → B) - (d₀₁ B).hom (Function.surjInv hψ m) with hb'_def
    have hψb' : ∀ g, ψ.hom (b' g) = 0 := fun g => by
      have h1 := congrFun hm g
      rw [Function.comp_apply] at h1
      rw [hb'_def, Pi.sub_apply, map_sub, ← h1, d₀₁_hom_apply, d₀₁_hom_apply, map_sub, Rep.hom_comm_apply, hσ,
        sub_self]
    set a : G → A := preimageFun φ ∘ b'
    have ha : ∀ g, φ.hom (a g) = b' g := fun g => apply_preimageFun φ ((hex _).1 (hψb' g))
    have ha' : φ.hom ∘ a = b' := funext ha
    have ha_coc : a ∈ cocycles₁ A := by
      show (d₁₂ A).hom a = 0
      have : φ.hom ∘ (d₁₂ A).hom a = 0 := by
        rw [← d₁₂_comp, ha', hb'_def, map_sub, d₁₂_cocycles₁, d₁₂_d₀₁, sub_zero]
      funext p; apply hφ; rw [Pi.zero_apply, map_zero]; simpa using congrFun this p
    refine ⟨⟨a, ha_coc⟩, (lc_sub₁ hb (isLevelConstant₁_d₀₁ (hsm (Function.surjInv hψ m)))).comp (preimageFun φ),
      Function.surjInv hψ m, ?_⟩
    show (d₀₁ B).hom (Function.surjInv hψ m) = (b : G → B) - φ.hom ∘ a
    rw [ha', hb'_def, sub_sub_cancel]
  · rintro ⟨a, ha, b₀, hb₀⟩
    refine ⟨ψ.hom b₀, funext fun g => ?_⟩
    have := congrFun hb₀ g
    rw [d₀₁_hom_apply, Pi.sub_apply, Function.comp_apply] at this
    rw [d₀₁_hom_apply, ← Rep.hom_comm_apply, ← map_sub, this, map_sub, Function.comp_apply,
      (hex _).2 ⟨a g, rfl⟩, sub_zero]

end S_groupCohomology_comp_mem_coboundaries1_iff_exists_isLevelConstant1_sub_comp
end P2MW
export P2MW.S_groupCohomology_comp_mem_coboundaries1_iff_exists_isLevelConstant1_sub_comp (solution)
