-- Prove2me | solution 1 for groupCohomology.finrank_continuousClasses_eq_finrank_of_isUnit_index_of_forall_apply_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/ad281a21-6b91-5a49-9a5b-3fd6bc0959f5

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Theorems.Thm_groupCohomology_exists_submodule_mem_iff_conjInvariant
import Theorems.Thm_groupCohomology_forall_exists_conj_sub_eq_iff_of_forall_apply_eq
import Theorems.Thm_groupCohomology_exists_linearEquiv_H1_of_forall_iff_of_isUnit_index
import Theorems.Thm_groupCohomology_cocycles1_conj_apply_sub_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_finrank_continuousClasses_eq_finrank_of_isUnit_index_of_forall_apply_eq

set_option autoImplicit false
universe u
open CategoryTheory Module groupCohomology
open scoped IntermediateField Pointwise

theorem solution
    {k G : Type u} [Field k] [Group G] (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (A : Rep.{u} k G) (S : Subgroup G) [S.Normal] [S.FiniteIndex]
    (hindex : IsUnit ((S.index : k)))
    (htriv : ∀ s ∈ S, ∀ v : A, A.ρ s v = v)
    (hS : ∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧
      ∀ s : G, r s ∈ F₀.fixingSubgroup → s ∈ S)
    (adm : Submodule k (H1 A))
    (hadm : ∀ x, x ∈ adm ↔ ∃ c : cocycles₁ A, IsLevelConstant₁ r c.val ∧ (H1π A).hom c = x)
    (W : Submodule k (cocycles₁ (Rep.res S.subtype A)))
    (hW : ∀ c, c ∈ W ↔ IsLevelConstant₁ (r.comp S.subtype) c.val ∧
      ∀ (g : G) (s t : S), (g⁻¹ * s * g : G) = t → A.ρ g (c t) = c s) :
    finrank k adm = finrank k W := by
  classical
  have htrivB : ∀ (s : S) (v : Rep.res S.subtype A), (Rep.res S.subtype A).ρ s v = v :=
    fun s v => htriv s s.2 v

  obtain ⟨V, hV⟩ := exists_submodule_mem_iff_conjInvariant A S
  obtain ⟨e, he⟩ := exists_linearEquiv_H1_of_forall_iff_of_isUnit_index A S hindex V hV

  let res : H1 A →ₗ[k] H1 (Rep.res S.subtype A) :=
    (map S.subtype (𝟙 (Rep.res S.subtype A)) 1).hom
  have he' : ∀ y : H1 A, ((e y : V) : H1 (Rep.res S.subtype A)) = res y := fun y => by
    rw [he, H1InfRes_g]
    rfl
  have hres_inj : Function.Injective res := by
    intro y y' h
    apply e.injective
    apply Subtype.ext
    rw [he', he']
    exact h
  have hres_π : ∀ c : cocycles₁ A, res ((H1π A).hom c) =
      (H1π (Rep.res S.subtype A)).hom (mapCocycles₁ S.subtype (𝟙 (Rep.res S.subtype A)) c) :=
    fun c => H1π_comp_map_apply S.subtype (𝟙 (Rep.res S.subtype A)) c
  have hmap : ∀ (c : cocycles₁ A) (s : S),
      (mapCocycles₁ S.subtype (𝟙 (Rep.res S.subtype A)) c) s = c (s : G) := by
    intro c s
    rw [coe_mapCocycles₁]
    rfl

  haveI : (Rep.res S.subtype A).IsTrivial := ⟨fun s => LinearMap.ext fun v => htrivB s v⟩
  have hπ_inj : Function.Injective (H1π (Rep.res S.subtype A)).hom := by
    intro c c' h
    have h' := (H1π_eq_iff c c').mp h
    rw [coboundaries₁_eq_bot_of_isTrivial, Submodule.mem_bot, sub_eq_zero] at h'
    exact DFunLike.coe_injective h'
  have hπ_surj : Function.Surjective (H1π (Rep.res S.subtype A)).hom := fun x =>
    H1_induction_on x (fun c => ⟨c, rfl⟩)
  let πB : cocycles₁ (Rep.res S.subtype A) ≃ₗ[k] H1 (Rep.res S.subtype A) :=
    LinearEquiv.ofBijective (H1π (Rep.res S.subtype A)).hom ⟨hπ_inj, hπ_surj⟩
  have hπB : ∀ c, πB c = (H1π (Rep.res S.subtype A)).hom c := fun _ => rfl

  let f₀ : adm →ₗ[k] cocycles₁ (Rep.res S.subtype A) := πB.symm.toLinearMap ∘ₗ res.domRestrict adm
  have hf₀ : ∀ (c : cocycles₁ A) (hc : (H1π A).hom c ∈ adm),
      f₀ ⟨(H1π A).hom c, hc⟩ = mapCocycles₁ S.subtype (𝟙 (Rep.res S.subtype A)) c := by
    intro c hc
    show πB.symm (res ((H1π A).hom c)) = _
    apply πB.injective
    rw [LinearEquiv.apply_symm_apply, hπB]
    exact hres_π c

  have hf₀W : ∀ x : adm, f₀ x ∈ W := by
    rintro ⟨x, hx⟩
    obtain ⟨c, ⟨F, hF, hlev⟩, rfl⟩ := (hadm x).mp hx
    rw [hf₀ c hx, hW]
    refine ⟨⟨F, hF, fun g s hs => ?_⟩, fun g s t hst => ?_⟩
    · show (mapCocycles₁ S.subtype (𝟙 (Rep.res S.subtype A)) c) (g * s) =
        (mapCocycles₁ S.subtype (𝟙 (Rep.res S.subtype A)) c) g
      rw [hmap, hmap, Subgroup.coe_mul]
      exact hlev g s hs
    · rw [hmap, hmap, ← hst]
      have h := cocycles1_conj_apply_sub_eq A c g s
      rwa [htriv s s.2, sub_self, sub_eq_zero] at h
  let Θ : adm →ₗ[k] W := f₀.codRestrict W hf₀W

  have hΘ_inj : Function.Injective Θ := by
    rintro ⟨x, hx⟩ ⟨x', hx'⟩ h
    apply Subtype.ext
    apply hres_inj
    have h' : f₀ ⟨x, hx⟩ = f₀ ⟨x', hx'⟩ := congrArg Subtype.val h
    have h'' : πB.symm (res x) = πB.symm (res x') := h'
    exact πB.symm.injective h''
  have hΘ_surj : Function.Surjective Θ := by
    rintro ⟨c, hc⟩
    obtain ⟨⟨F, hF, hlev⟩, hconj⟩ := (hW c).mp hc

    have hcV : (H1π (Rep.res S.subtype A)).hom c ∈ V := (hV _).mpr ⟨c, rfl,
      (forall_exists_conj_sub_eq_iff_of_forall_apply_eq A S htriv c).mpr hconj⟩

    obtain ⟨c0, hc0⟩ : ∃ c0 : cocycles₁ A, (H1π A).hom c0 = e.symm ⟨_, hcV⟩ :=
      H1_induction_on (C := fun y => ∃ c0 : cocycles₁ A, (H1π A).hom c0 = y) (e.symm ⟨_, hcV⟩)
        (fun c0 => ⟨c0, rfl⟩)
    have hres0 : res ((H1π A).hom c0) = (H1π (Rep.res S.subtype A)).hom c := by
      rw [hc0, ← he', LinearEquiv.apply_symm_apply]
    have hc0c : mapCocycles₁ S.subtype (𝟙 (Rep.res S.subtype A)) c0 = c :=
      hπ_inj ((hres_π c0).symm.trans hres0)
    have hc0s : ∀ s : S, c0 (s : G) = c s := fun s => by rw [← hc0c, hmap]
    obtain ⟨F₀, hF₀, hS₀⟩ := hS
    haveI := hF
    haveI := hF₀
    have hc0lev : IsLevelConstant₁ r c0.val := by
      refine ⟨F ⊔ F₀, inferInstance, fun g u hu => ?_⟩
      have huS : u ∈ S := hS₀ u (IntermediateField.fixingSubgroup_antitone le_sup_right hu)
      have huF : r u ∈ F.fixingSubgroup := IntermediateField.fixingSubgroup_antitone le_sup_left hu
      have hcu : c0 u = 0 := by
        rw [show u = ((⟨u, huS⟩ : S) : G) from rfl, hc0s]
        have h1 := hlev 1 ⟨u, huS⟩ huF
        rw [one_mul] at h1
        exact h1.trans (cocycles₁_map_one c)
      show c0 (g * u) = c0 g
      rw [(mem_cocycles₁_iff c0).mp c0.2 g u, hcu, map_zero, zero_add]
    have hy_adm : (H1π A).hom c0 ∈ adm := (hadm _).mpr ⟨c0, hc0lev, rfl⟩
    refine ⟨⟨(H1π A).hom c0, hy_adm⟩, Subtype.ext ?_⟩
    show f₀ ⟨(H1π A).hom c0, hy_adm⟩ = c
    rw [hf₀, hc0c]
  exact LinearEquiv.finrank_eq (LinearEquiv.ofBijective Θ ⟨hΘ_inj, hΘ_surj⟩)

end S_groupCohomology_finrank_continuousClasses_eq_finrank_of_isUnit_index_of_forall_apply_eq
end P2MW
export P2MW.S_groupCohomology_finrank_continuousClasses_eq_finrank_of_isUnit_index_of_forall_apply_eq (solution)
