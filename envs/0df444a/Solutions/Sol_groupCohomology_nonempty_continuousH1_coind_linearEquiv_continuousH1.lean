-- Prove2me | solution 1 for groupCohomology.nonempty_continuousH1_coind_linearEquiv_continuousH1
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/9827ef3a-2e8a-5772-8a7e-b91d5042afb5

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_LevelSubgroup
import Definitions.Def_GroupCohomology_ContinuousH2Map
import Definitions.Def_GroupCohomology_ContinuousH1
import Theorems.Thm_groupCohomology_coind_cocycles1_mem_coboundaries1_of_eval_one_mem_coboundaries1
import Theorems.Thm_groupCohomology_exists_coind_cocycles1_isLevelConstant1_eval_one_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_nonempty_continuousH1_coind_linearEquiv_continuousH1

set_option autoImplicit false

universe u

open CategoryTheory

open groupCohomology in
theorem solution {k G : Type u} [CommRing k] [Group G]
    (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (S : Subgroup G)
    (hS : ∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧ F₀.fixingSubgroup.comap r ≤ S)
    (N : Rep.{u} k S) :
    Nonempty (groupCohomology.continuousH1 r (Rep.coind S.subtype N)
      ≃ₗ[k] groupCohomology.continuousH1 (r.comp S.subtype) N) := by
  classical

  let evL : (Rep.coind S.subtype N) →ₗ[k] N :=
    { toFun := fun f => (f : G → N) 1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let ev : Rep.res S.subtype (Rep.coind S.subtype N) ⟶ N :=
    Rep.ofHom (evL.intertwiningMap_of_isIntertwiningMap ((Rep.coind S.subtype N).ρ.comp S.subtype) N.ρ
      fun s f => by
        show ((f : Rep.coind S.subtype N) : G → N) (1 * (s : G)) = N.ρ s (((f : Rep.coind S.subtype N) : G → N) 1)
        rw [one_mul, ← mul_one (s : G)]
        exact (f : Rep.coind S.subtype N).2 s 1)
  have coe_map : ∀ c : cocycles₁ (Rep.coind S.subtype N),
      (mapCocycles₁ S.subtype ev c : S → N) = fun s : S => ((c (s : G) : Rep.coind S.subtype N) : G → N) 1 :=
    fun _ => rfl
  have Hmap : ∀ c : cocycles₁ (Rep.coind S.subtype N),
      (map S.subtype ev 1).hom ((H1π _).hom c) = (H1π N).hom (mapCocycles₁ S.subtype ev c) :=
    fun c => H1π_comp_map_apply S.subtype ev c

  have hmapsto : ∀ x : continuousH1 r (Rep.coind S.subtype N),
      (map S.subtype ev 1).hom (x : H1 (Rep.coind S.subtype N)) ∈ continuousH1 (r.comp S.subtype) N := by
    intro x
    obtain ⟨c, ⟨F, hF, hc⟩, hx⟩ := (mem_continuousH1_iff r _ _).1 x.2
    rw [← hx, Hmap]
    refine H1π_mem_continuousH1 _ N ⟨F, hF, fun s s' hs' => ?_⟩
    rw [coe_map]
    show ((c ((s * s' : S) : G) : Rep.coind S.subtype N) : G → N) 1 = ((c (s : G) : Rep.coind S.subtype N) : G → N) 1
    rw [Subgroup.coe_mul, hc (s : G) (s' : G) hs']
  let Sh : continuousH1 r (Rep.coind S.subtype N) →ₗ[k] continuousH1 (r.comp S.subtype) N :=
    ((map S.subtype ev 1).hom ∘ₗ (continuousH1 r _).subtype).codRestrict _ hmapsto
  refine ⟨LinearEquiv.ofBijective Sh ⟨?_, ?_⟩⟩
  ·
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    obtain ⟨c, hclc, hcx⟩ := (mem_continuousH1_iff r _ _).1 x.2
    have h0 : (map S.subtype ev 1).hom ((H1π _).hom c) = 0 := by
      rw [hcx]; exact congrArg Subtype.val hx
    rw [Hmap, show (H1π N).hom (mapCocycles₁ S.subtype ev c) = 0 ↔ _ from H1π_eq_zero_iff _, coe_map] at h0
    have := groupCohomology.coind_cocycles1_mem_coboundaries1_of_eval_one_mem_coboundaries1 S N c h0
    apply Subtype.ext
    rw [← hcx, Submodule.coe_zero]
    exact (show (H1π _).hom c = 0 ↔ _ from H1π_eq_zero_iff c).2 this
  ·
    intro y
    obtain ⟨b, hb, hby⟩ := (mem_continuousH1_iff _ N _).1 y.2
    obtain ⟨c, hc, hev⟩ :=
      groupCohomology.exists_coind_cocycles1_isLevelConstant1_eval_one_eq r S hS N b hb
    refine ⟨⟨(H1π _).hom c, H1π_mem_continuousH1 r _ hc⟩, Subtype.ext ?_⟩
    show (map S.subtype ev 1).hom ((H1π _).hom c) = (y : H1 N)
    rw [Hmap, ← hby]
    congr 1
    apply cocycles₁_ext
    intro s
    rw [coe_map]
    exact hev s

end S_groupCohomology_nonempty_continuousH1_coind_linearEquiv_continuousH1
end P2MW
export P2MW.S_groupCohomology_nonempty_continuousH1_coind_linearEquiv_continuousH1 (solution)
