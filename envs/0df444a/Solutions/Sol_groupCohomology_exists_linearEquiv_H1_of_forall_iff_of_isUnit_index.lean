-- Prove2me | solution 1 for groupCohomology.exists_linearEquiv_H1_of_forall_iff_of_isUnit_index
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/7997097a-468b-583f-8add-2462debf732c

import Mathlib
import Theorems.Thm_groupCohomology_mem_coboundaries1_of_restrict_of_isUnit_index
import Theorems.Thm_groupCohomology_cocycles1_conj_apply_sub_eq
import Theorems.Thm_groupCohomology_exists_cocycles1_restrict_eq_add_of_isUnit_index
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_exists_linearEquiv_H1_of_forall_iff_of_isUnit_index

set_option autoImplicit false

universe u

open CategoryTheory groupCohomology

theorem solution
    {k G : Type u} [CommRing k] [Group G] (A : Rep.{u} k G) (S : Subgroup G) [S.Normal]
    [S.FiniteIndex] (hindex : IsUnit ((S.index : k)))
    (V : Submodule k (H1 (Rep.res S.subtype A)))
    (hV : ∀ x, x ∈ V ↔ ∃ c : cocycles₁ (Rep.res S.subtype A), H1π _ c = x ∧
      ∀ g : G, ∃ a : A, ∀ s t : S, (g⁻¹ * s * g : G) = t →
        A.ρ g (c t) - c s = A.ρ (s : G) a - a) :
    ∃ e : H1 A ≃ₗ[k] V, ∀ y : H1 A,
      ((e y : V) : H1 (Rep.res S.subtype A)) = (H1InfRes A S).g.hom y := by
  classical
  let res : H1 A →ₗ[k] H1 (Rep.res S.subtype A) := (H1InfRes A S).g.hom

  let rc : cocycles₁ A → cocycles₁ (Rep.res S.subtype A) :=
    fun c => mapCocycles₁ S.subtype (𝟙 (Rep.res S.subtype A)) c
  have hrc : ∀ (c : cocycles₁ A) (s : S), rc c s = c (s : G) := fun c s => by
    show (mapCocycles₁ S.subtype (𝟙 (Rep.res S.subtype A)) c : S → A) s = c (s : G)
    rw [coe_mapCocycles₁]; rfl
  have hres : ∀ c : cocycles₁ A, res (H1π A c) = H1π _ (rc c) := fun c => by
    have h__af := H1π_comp_map_apply S.subtype (𝟙 (Rep.res S.subtype A)) c
    simp only [H1InfRes_g] at h__af
    exact h__af

  have hmem : ∀ y : H1 A, res y ∈ V := by
    intro y
    induction y using H1_induction_on with | h c =>
    rw [hres, hV]
    refine ⟨rc c, rfl, fun g => ⟨c g, fun s t hst => ?_⟩⟩
    rw [hrc, hrc, ← hst]
    exact cocycles1_conj_apply_sub_eq A c g s

  have hinj : Function.Injective res := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    induction y using H1_induction_on with | h c =>
    rw [hres, H1π_eq_zero_iff] at hy
    obtain ⟨a, ha⟩ := hy
    have ha' : ∀ s : S, c (s : G) = A.ρ (s : G) a - a := fun s => by
      have h1 := congrFun ha s
      rw [d₀₁_hom_apply] at h1
      rw [← hrc, ← h1]; rfl
    obtain ⟨b, hb⟩ := mem_coboundaries1_of_restrict_of_isUnit_index A S hindex c ⟨a, ha'⟩
    exact (H1π_eq_zero_iff c).2 ⟨b, funext fun g => by rw [d₀₁_hom_apply]; exact (hb g).symm⟩

  have hsurj : ∀ x ∈ V, ∃ y : H1 A, res y = x := by
    intro x hx
    obtain ⟨c, rfl, hc⟩ := (hV x).1 hx
    obtain ⟨c', a, hc'⟩ := exists_cocycles1_restrict_eq_add_of_isUnit_index A S hindex c hc
    refine ⟨H1π A c', ?_⟩
    rw [hres, H1π_eq_iff]
    refine ⟨a, funext fun s => ?_⟩
    rw [d₀₁_hom_apply, Pi.sub_apply, hrc, hc']
    show A.ρ (s : G) a - a = c s + ((A.ρ (s : G)) a - a) - c s
    abel
  let f : H1 A →ₗ[k] V := LinearMap.codRestrict V res hmem
  refine ⟨LinearEquiv.ofBijective f ⟨fun y y' h => hinj (congrArg Subtype.val h),
    fun ⟨x, hx⟩ => ?_⟩, fun y => rfl⟩
  obtain ⟨y, hy⟩ := hsurj x hx
  exact ⟨y, Subtype.ext hy⟩

end S_groupCohomology_exists_linearEquiv_H1_of_forall_iff_of_isUnit_index
end P2MW
export P2MW.S_groupCohomology_exists_linearEquiv_H1_of_forall_iff_of_isUnit_index (solution)
