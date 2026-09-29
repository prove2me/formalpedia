-- Prove2me | solution 1 for groupCohomology.comp_mem_levelCoboundaries2_iff_exists_sub_deltaCochain1
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/36b222c3-1e42-506a-b75e-a14b3678a8d3

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_ContinuousH2Map
import Definitions.Def_GroupCohomology_ContinuousH1
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_comp_mem_levelCoboundaries2_iff_exists_sub_deltaCochain1

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
    (a : G × G → A) :
    (φ.hom ∘ a) ∈ groupCohomology.levelCoboundaries₂ r B ↔
      ∃ c : groupCohomology.cocycles₁ C, groupCohomology.IsLevelConstant₁ r c ∧
        (a - groupCohomology.deltaCochain₁ φ ψ hψ c) ∈ groupCohomology.levelCoboundaries₂ r A := by
  have hσ : ∀ x : C, ψ.hom (Function.surjInv hψ x) = x := Function.surjInv_eq hψ
  constructor
  · intro h
    obtain ⟨bt, hbt_lc, hbt⟩ := (mem_levelCoboundaries₂_iff r B _).1 h

    have hc_coc : (ψ.hom ∘ bt) ∈ cocycles₁ C := by
      show (d₁₂ C).hom (ψ.hom ∘ bt) = 0
      rw [d₁₂_comp ψ, hbt]
      funext p; exact (hex _).2 ⟨a p, rfl⟩
    set c : cocycles₁ C := ⟨ψ.hom ∘ bt, hc_coc⟩
    have hc_lc : IsLevelConstant₁ r c := hbt_lc.comp _
    refine ⟨c, hc_lc, ?_⟩

    set eA : G → A := preimageFun φ ∘ (Function.surjInv hψ ∘ c - bt)
    have heA : ∀ g, φ.hom (eA g) = Function.surjInv hψ (c g) - bt g := fun g =>
      apply_preimageFun φ ((hex _).1 (by rw [Pi.sub_apply, map_sub, Function.comp_apply, hσ]; exact sub_self _))
    have heA_lc : IsLevelConstant₁ r eA := (lc_sub₁ (hc_lc.comp _) hbt_lc).comp _
    have hker : ∀ p, ψ.hom ((d₁₂ B).hom (Function.surjInv hψ ∘ c) p) = 0 := by
      rintro ⟨g, h⟩
      rw [d₁₂_hom_apply, map_add, map_sub, Rep.hom_comm_apply, Function.comp_apply, Function.comp_apply,
        Function.comp_apply, hσ, hσ, hσ, (mem_cocycles₁_iff (c : G → C)).1 c.2 g h]
      abel
    have hφδ : ∀ p, φ.hom (deltaCochain₁ φ ψ hψ c p) = (d₁₂ B).hom (Function.surjInv hψ ∘ c) p := fun p =>
      apply_preimageFun φ ((hex _).1 (hker p))

    refine (mem_levelCoboundaries₂_iff r A _).2 ⟨-eA, ?_, funext fun p => hφ ?_⟩
    · obtain ⟨F, hF, hF'⟩ := heA_lc
      exact ⟨F, hF, fun g s hs => by simp only [Pi.neg_apply, hF' g s hs]⟩
    have e1 : φ.hom ∘ eA = Function.surjInv hψ ∘ ⇑c - bt := funext heA
    have e2 : φ.hom ((d₁₂ A).hom (-eA) p)
        = -((d₁₂ B).hom (Function.surjInv hψ ∘ ⇑c) p - (d₁₂ B).hom bt p) := by
      rw [map_neg, Pi.neg_apply, map_neg,
        show φ.hom ((d₁₂ A).hom eA p) = (d₁₂ B).hom (φ.hom ∘ eA) p by rw [d₁₂_comp]; rfl,
        e1, map_sub, Pi.sub_apply]
    rw [e2, Pi.sub_apply, map_sub, hφδ, hbt, Function.comp_apply]
    abel
  · rintro ⟨c, hc_lc, eA, heA_lc, heA⟩
    have hker : ∀ p, ψ.hom ((d₁₂ B).hom (Function.surjInv hψ ∘ c) p) = 0 := by
      rintro ⟨g, h⟩
      rw [d₁₂_hom_apply, map_add, map_sub, Rep.hom_comm_apply, Function.comp_apply, Function.comp_apply,
        Function.comp_apply, hσ, hσ, hσ, (mem_cocycles₁_iff (c : G → C)).1 c.2 g h]
      abel
    have hφδ : ∀ p, φ.hom (deltaCochain₁ φ ψ hψ c p) = (d₁₂ B).hom (Function.surjInv hψ ∘ c) p := fun p =>
      apply_preimageFun φ ((hex _).1 (hker p))

    refine (mem_levelCoboundaries₂_iff r B _).2
      ⟨Function.surjInv hψ ∘ c + φ.hom ∘ eA, (hc_lc.comp _).add (heA_lc.comp _), funext fun p => ?_⟩
    rw [map_add, d₁₂_comp, Pi.add_apply, Function.comp_apply, heA, Pi.sub_apply, map_sub, hφδ,
      Function.comp_apply]
    abel

end S_groupCohomology_comp_mem_levelCoboundaries2_iff_exists_sub_deltaCochain1
end P2MW
export P2MW.S_groupCohomology_comp_mem_levelCoboundaries2_iff_exists_sub_deltaCochain1 (solution)
