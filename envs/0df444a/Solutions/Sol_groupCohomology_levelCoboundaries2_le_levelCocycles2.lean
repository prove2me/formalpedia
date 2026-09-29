-- Prove2me | solution 1 for groupCohomology.levelCoboundaries2_le_levelCocycles2
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/449c7ffe-29cd-5245-afc0-cebd2cd68fad

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_levelCoboundaries2_le_levelCocycles2

set_option autoImplicit false

universe u

namespace P2mS26U1

open IntermediateField

variable {G : Type*} [Group G]

theorem comap_fixingSubgroup_eq_ker (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [Normal ℚ F] :
    F.fixingSubgroup.comap r
      = ((AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) F).comp r).ker := by
  rw [← @IntermediateField.restrictNormalHom_ker ℚ (AlgebraicClosure ℚ) _ _ _ F ‹Normal ℚ F›,
    MonoidHom.comap_ker]
  rfl

theorem normal_comap_fixingSubgroup (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [Normal ℚ F] :
    (F.fixingSubgroup.comap r).Normal := by
  rw [comap_fixingSubgroup_eq_ker]; exact MonoidHom.normal_ker _

theorem finiteIndex_comap_fixingSubgroup (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ F] [Normal ℚ F] :
    (F.fixingSubgroup.comap r).FiniteIndex := by
  rw [comap_fixingSubgroup_eq_ker]; exact Subgroup.finiteIndex_ker _

end P2mS26U1

namespace P2mS26U1

theorem exists_isGalois_ge (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ F] :
    ∃ F' : IntermediateField ℚ (AlgebraicClosure ℚ),
      FiniteDimensional ℚ F' ∧ IsGalois ℚ F' ∧ F ≤ F' := by
  haveI : Normal ℚ (AlgebraicClosure ℚ) := by
    convert @IsAlgClosure.normal ℚ (AlgebraicClosure ℚ) _ _ (AlgebraicClosure.instAlgebra ℚ) inferInstance
    exact Subsingleton.elim _ _
  let L : IntermediateField ℚ (AlgebraicClosure ℚ) := IntermediateField.normalClosure ℚ F (AlgebraicClosure ℚ)
  haveI : FiniteDimensional ℚ L := normalClosure.is_finiteDimensional ℚ F (AlgebraicClosure ℚ)
  haveI : Normal ℚ L := normalClosure.normal ℚ F (AlgebraicClosure ℚ)
  haveI : IsGalois ℚ L := ⟨⟩
  exact ⟨L, inferInstance, inferInstance, IntermediateField.le_normalClosure F⟩

end P2mS26U1

theorem P2mS26U1.exists_isGalois₁ {G : Type u} [Group G]
    {r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)} {X : Type*} {f : G → X}
    (hf : groupCohomology.IsLevelConstant₁ r f) :
    ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧ IsGalois ℚ F ∧
      ∀ g s : G, r s ∈ F.fixingSubgroup → f (g * s) = f g ∧ f (s * g) = f g := by
  obtain ⟨F₀, hF₀, h⟩ := hf
  haveI := hF₀
  obtain ⟨F, hF, hG, hle⟩ := P2mS26U1.exists_isGalois_ge F₀
  haveI := hG
  have hN := P2mS26U1.normal_comap_fixingSubgroup r F
  refine ⟨F, hF, hG, fun g s hs => ⟨h g s (IntermediateField.fixingSubgroup_antitone hle hs), ?_⟩⟩
  have hs' : g⁻¹ * s * g ∈ F.fixingSubgroup.comap r := by
    simpa using hN.conj_mem s hs g⁻¹
  have := h g (g⁻¹ * s * g) (IntermediateField.fixingSubgroup_antitone hle hs')
  rwa [show g * (g⁻¹ * s * g) = s * g by group] at this

open groupCohomology in
theorem solution {k G : Type u} [CommRing k] [Group G]
    (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (M : Rep k G)
    (hsm : ∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s, r s ∈ F.fixingSubgroup → M.ρ s m = m) :
    groupCohomology.levelCoboundaries₂ r M ≤ groupCohomology.levelCocycles₂ r M := by
  classical
  intro f hf
  refine ⟨levelCoboundaries₂_le_cocycles₂ r M hf, ?_⟩
  obtain ⟨x, hx, rfl⟩ := (mem_levelCoboundaries₂_iff r M f).1 hf
  show IsLevelConstant₂ r ((d₁₂ M).hom x)
  obtain ⟨F₁, hF₁, hG₁, h₁⟩ := P2mS26U1.exists_isGalois₁ hx
  haveI := hF₁; haveI := hG₁
  haveI : (F₁.fixingSubgroup.comap r).FiniteIndex := P2mS26U1.finiteIndex_comap_fixingSubgroup r F₁
  have hN : (F₁.fixingSubgroup.comap r).Normal := P2mS26U1.normal_comap_fixingSubgroup r F₁

  have hwd : ∀ a b : G,
      @Setoid.r _ (QuotientGroup.leftRel (F₁.fixingSubgroup.comap r)) a b → x a = x b := by
    intro a b hab
    have hab' : a⁻¹ * b ∈ F₁.fixingSubgroup.comap r := QuotientGroup.leftRel_apply.mp hab
    have := (h₁ a (a⁻¹ * b) hab').1
    rw [mul_inv_cancel_left] at this
    exact this.symm
  haveI : Finite (G ⧸ F₁.fixingSubgroup.comap r) := Subgroup.finite_quotient_of_finiteIndex
  have hfin : (Set.range x).Finite := by
    refine (Set.finite_range
      (show G ⧸ F₁.fixingSubgroup.comap r → M from
        @Quotient.lift _ _ (QuotientGroup.leftRel (F₁.fixingSubgroup.comap r)) x hwd)).subset ?_
    rintro _ ⟨g, rfl⟩
    exact ⟨(g : G ⧸ F₁.fixingSubgroup.comap r), rfl⟩
  haveI := hfin.to_subtype

  choose Fv hFv hfix using fun v : Set.range x => hsm (v : M)
  haveI := hFv
  haveI : FiniteDimensional ℚ (⨆ v, Fv v : IntermediateField ℚ (AlgebraicClosure ℚ)) :=
    IntermediateField.finiteDimensional_iSup_of_finite
  refine ⟨F₁ ⊔ ⨆ v, Fv v, inferInstance, fun g g' s s' hs hs' => ?_⟩
  have hs₁ : r s ∈ F₁.fixingSubgroup := IntermediateField.fixingSubgroup_antitone le_sup_left hs
  have hs'₁ : r s' ∈ F₁.fixingSubgroup := IntermediateField.fixingSubgroup_antitone le_sup_left hs'
  have hs₂ : ∀ h : G, M.ρ s (x h) = x h := fun h =>
    hfix ⟨x h, h, rfl⟩ s
      (IntermediateField.fixingSubgroup_antitone ((le_iSup Fv _).trans le_sup_right) hs)
  have e : ∀ a b : G, (d₁₂ M).hom x (a, b) = M.ρ a (x b) - x (a * b) + x a :=
    fun a b => d₁₂_hom_apply M x (a, b)
  rw [e, e, (h₁ g' s' hs'₁).1, (h₁ g s hs₁).1, map_mul, Module.End.mul_apply, hs₂ g',
    show g * s * (g' * s') = g * g' * (g'⁻¹ * s * g') * s' by group, (h₁ _ s' hs'₁).1]
  have hc : g'⁻¹ * s * g' ∈ F₁.fixingSubgroup.comap r := by simpa using hN.conj_mem s hs₁ g'⁻¹
  rw [(h₁ _ _ hc).1]

end S_groupCohomology_levelCoboundaries2_le_levelCocycles2
end P2MW
export P2MW.S_groupCohomology_levelCoboundaries2_le_levelCocycles2 (solution)
