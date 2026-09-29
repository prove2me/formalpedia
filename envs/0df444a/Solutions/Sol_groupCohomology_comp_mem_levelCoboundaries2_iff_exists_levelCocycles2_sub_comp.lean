-- Prove2me | solution 1 for groupCohomology.comp_mem_levelCoboundaries2_iff_exists_levelCocycles2_sub_comp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/c88fc46d-7ff6-5c3d-98c7-cf16758e7912

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_ContinuousH2Map
import Definitions.Def_GroupCohomology_ContinuousH1
import Theorems.Thm_groupCohomology_levelCoboundaries2_le_levelCocycles2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_comp_mem_levelCoboundaries2_iff_exists_levelCocycles2_sub_comp

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
    (b : G × G → B) (hb : b ∈ groupCohomology.levelCocycles₂ r B) :
    (ψ.hom ∘ b) ∈ groupCohomology.levelCoboundaries₂ r C ↔
      ∃ a ∈ groupCohomology.levelCocycles₂ r A, (b - φ.hom ∘ a) ∈ groupCohomology.levelCoboundaries₂ r B := by
  have hσ : ∀ x : C, ψ.hom (Function.surjInv hψ x) = x := Function.surjInv_eq hψ
  constructor
  · intro h
    obtain ⟨ct, hct_lc, hct⟩ := (mem_levelCoboundaries₂_iff r C _).1 h
    set bt : G → B := Function.surjInv hψ ∘ ct
    have hbt_lc : IsLevelConstant₁ r bt := hct_lc.comp _
    have hdbt : (d₁₂ B).hom bt ∈ levelCocycles₂ r B :=
      groupCohomology.levelCoboundaries2_le_levelCocycles2 r B hsm
        ((mem_levelCoboundaries₂_iff r B _).2 ⟨bt, hbt_lc, rfl⟩)
    have hψd : ψ.hom ∘ (d₁₂ B).hom bt = ψ.hom ∘ b := by
      rw [← hct, ← d₁₂_comp ψ]
      congr 1; funext g; exact hσ (ct g)

    set a : G × G → A := preimageFun φ ∘ (b - (d₁₂ B).hom bt)
    have ha : ∀ p, φ.hom (a p) = b p - (d₁₂ B).hom bt p := fun p =>
      apply_preimageFun φ ((hex _).1 (by
        rw [Pi.sub_apply, map_sub, sub_eq_zero]; exact (congrFun hψd p).symm))
    have ha' : φ.hom ∘ a = b - (d₁₂ B).hom bt := funext ha
    refine ⟨a, ⟨?_, (lc_sub₂ hb.2 hdbt.2).comp _⟩, ?_⟩
    · show (d₂₃ A).hom a = 0
      have : φ.hom ∘ (d₂₃ A).hom a = 0 := by
        rw [← d₂₃_comp, ha', map_sub, d₂₃_cocycles₂ hb.1, d₂₃_d₁₂, sub_zero]
      funext p; apply hφ; rw [Pi.zero_apply, map_zero]; simpa using congrFun this p
    · rw [ha']
      refine (mem_levelCoboundaries₂_iff r B _).2 ⟨bt, hbt_lc, ?_⟩
      abel
  · rintro ⟨a, ha, bt, hbt_lc, hbt⟩
    refine (mem_levelCoboundaries₂_iff r C _).2 ⟨ψ.hom ∘ bt, hbt_lc.comp _, ?_⟩
    rw [d₁₂_comp ψ, hbt]
    funext p
    simp only [Function.comp_apply, Pi.sub_apply, map_sub, (hex _).2 ⟨a p, rfl⟩, sub_zero]

end S_groupCohomology_comp_mem_levelCoboundaries2_iff_exists_levelCocycles2_sub_comp
end P2MW
export P2MW.S_groupCohomology_comp_mem_levelCoboundaries2_iff_exists_levelCocycles2_sub_comp (solution)
