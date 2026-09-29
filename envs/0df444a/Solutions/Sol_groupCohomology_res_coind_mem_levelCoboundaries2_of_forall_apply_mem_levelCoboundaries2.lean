-- Prove2me | solution 1 for groupCohomology.res_coind_mem_levelCoboundaries2_of_forall_apply_mem_levelCoboundaries2
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/3079ec97-11d4-52c3-a456-a316f41c36a1

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_ContinuousH2Map
import Definitions.Def_GroupCohomology_LevelSubgroup
import Theorems.Thm_Rep_exists_res_coind_linearEquiv_coind_comap
import Theorems.Thm_groupCohomology_coind_mem_levelCoboundaries2_of_eval_one_mem_levelCoboundaries2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_res_coind_mem_levelCoboundaries2_of_forall_apply_mem_levelCoboundaries2

set_option autoImplicit false

universe u

open CategoryTheory groupCohomology

noncomputable section

namespace P2MShMInj

local notation "Γ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

variable {k : Type u} [CommRing k] {V : Type u} [AddCommGroup V] [Module k V]
  {G : Type u} [Group G] (r : G →* Γ) (U : Subgroup Γ)

abbrev T : Type := Γ ⧸ (U ⊔ r.range)

abbrev P : Rep k G := Rep.res r (Rep.coind U.subtype (Rep.trivial k ↥U V))

abbrev Q : Rep k G := Rep.coind (U.comap r).subtype (Rep.trivial k ↥(U.comap r) (T r U → V))

lemma finite_T (hUo : ∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧ F₀.fixingSubgroup ≤ U) :
    Finite (T r U) := by
  obtain ⟨F₀, hF₀, hle⟩ := hUo
  haveI := hF₀
  haveI : Normal ℚ (AlgebraicClosure ℚ) := by
    convert @IsAlgClosure.normal ℚ (AlgebraicClosure ℚ) _ _ (AlgebraicClosure.instAlgebra ℚ) inferInstance
    rfl
  haveI : Normal ℚ (IntermediateField.normalClosure ℚ F₀ (AlgebraicClosure ℚ)) :=
    normalClosure.normal ℚ F₀ (AlgebraicClosure ℚ)
  haveI h1 : (IntermediateField.normalClosure ℚ F₀ (AlgebraicClosure ℚ)).fixingSubgroup.FiniteIndex := by
    have := groupCohomology.finiteIndex_comap_fixingSubgroup (MonoidHom.id Γ)
      (IntermediateField.normalClosure ℚ F₀ (AlgebraicClosure ℚ))
    rwa [Subgroup.comap_id] at this
  have hle' : (IntermediateField.normalClosure ℚ F₀ (AlgebraicClosure ℚ)).fixingSubgroup ≤ U ⊔ r.range :=
    ((IntermediateField.fixingSubgroup_antitone (IntermediateField.le_normalClosure F₀)).trans hle).trans le_sup_left
  haveI : (U ⊔ r.range).FiniteIndex := Subgroup.finiteIndex_of_le hle'
  exact Subgroup.finite_quotient_of_finiteIndex

variable [U.Normal]
  (hU : ∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧ F₀.fixingSubgroup ≤ U)
  (γ : T r U → Γ) (hγ : ∀ t, (γ t : T r U) = t)

omit [U.Normal] in

lemma symm_equivariant (e : P (k := k) (V := V) r U ≃ₗ[k] Q (k := k) (V := V) r U)
    (he : ∀ (g : G) (f : P (k := k) (V := V) r U), e ((P r U).ρ g f) = (Q r U).ρ g (e f))
    (g : G) (q : Q (k := k) (V := V) r U) :
    e.symm ((Q r U).ρ ((MonoidHom.id G) g) q) = (P r U).ρ g (e.symm q) := by
  apply e.injective
  rw [LinearEquiv.apply_symm_apply, he, LinearEquiv.apply_symm_apply, MonoidHom.id_apply]

include hU hγ in

theorem main (c : G × G → P (k := k) (V := V) r U) (hc : c ∈ levelCocycles₂ r (P r U))
    (h : ∀ t, (fun d : ↥(U.comap r) × ↥(U.comap r) =>
        ((c ((d.1 : G), (d.2 : G)) : Rep.coind U.subtype (Rep.trivial k ↥U V)) : Γ → V) (γ t))
      ∈ levelCoboundaries₂ (r.comp (U.comap r).subtype) (Rep.trivial k ↥(U.comap r) V)) :
    c ∈ levelCoboundaries₂ r (P r U) := by
  haveI : Finite (T r U) := finite_T r U hU
  obtain ⟨e, he, hef⟩ := Rep.exists_res_coind_linearEquiv_coind_comap (k := k) (V := V) r U γ hγ

  have he' : ∀ (g : G) (f : P (k := k) (V := V) r U), e ((P r U).ρ ((MonoidHom.id G) g) f) = (Q r U).ρ g (e f) :=
    fun g f => he g f
  have hC : cochainsPullPush₂ (A := P r U) (B := Q r U) (MonoidHom.id G) e.toLinearMap c ∈ levelCocycles₂ r (Q r U) :=
    cochainsPullPush₂_mem_levelCocycles₂ (rH := r) (rG := r) (A := P r U) (B := Q r U) (MonoidHom.id G)
      (fun _ => rfl) e.toLinearMap he' hc

  choose E hE hdE using fun t => (mem_levelCoboundaries₂_iff _ _ _).1 (h t)
  have hK : (fun d : ↥(U.comap r) × ↥(U.comap r) =>
      ((cochainsPullPush₂ (A := P r U) (B := Q r U) (MonoidHom.id G) e.toLinearMap c ((d.1 : G), (d.2 : G)) : Q r U) :
        G → T r U → V) 1) ∈ levelCoboundaries₂ (r.comp (U.comap r).subtype) (Rep.trivial k ↥(U.comap r) (T r U → V)) := by
    refine (mem_levelCoboundaries₂_iff _ _ _).2 ⟨fun d t => E t d, ?_, ?_⟩
    · choose F hF hcst using hE
      haveI : ∀ t, FiniteDimensional ℚ (F t) := hF
      refine ⟨⨆ t, F t, IntermediateField.finiteDimensional_iSup_of_finite, fun g s hs => ?_⟩
      funext t
      exact hcst t g s (IntermediateField.fixingSubgroup_antitone (le_iSup F t) hs)
    · funext d
      funext t
      have h1 := congrFun (hdE t) d
      rw [d₁₂_hom_apply, Rep.trivial_ρ_apply] at h1
      rw [d₁₂_hom_apply, Rep.trivial_ρ_apply, cochainsPullPush₂_apply, MonoidHom.id_apply, MonoidHom.id_apply,
        LinearEquiv.coe_toLinearMap, hef, map_one, mul_one]
      simpa using h1
  have hS : ∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧
      F₀.fixingSubgroup.comap r ≤ U.comap r := by
    obtain ⟨F₀, hF₀, hle⟩ := hU
    exact ⟨F₀, hF₀, Subgroup.comap_mono hle⟩
  have hCb := groupCohomology.coind_mem_levelCoboundaries2_of_eval_one_mem_levelCoboundaries2 r (U.comap r) hS
    (Rep.trivial k ↥(U.comap r) (T r U → V)) _ hC hK
  have hback : c = cochainsPullPush₂ (A := Q r U) (B := P r U) (MonoidHom.id G) e.symm.toLinearMap
      (cochainsPullPush₂ (A := P r U) (B := Q r U) (MonoidHom.id G) e.toLinearMap c) := by
    funext gg
    rw [cochainsPullPush₂_apply, cochainsPullPush₂_apply]
    simp
  rw [hback]
  exact cochainsPullPush₂_mem_levelCoboundaries₂ (rH := r) (rG := r) (A := Q r U) (B := P r U) (MonoidHom.id G)
    (fun _ => rfl) e.symm.toLinearMap (symm_equivariant r U e he) hCb

end P2MShMInj

end

theorem solution {k : Type u} [CommRing k] {V : Type u} [AddCommGroup V] [Module k V]
    {G : Type u} [Group G] (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (U : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) [U.Normal]
    (hU : ∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧ F₀.fixingSubgroup ≤ U)
    (γ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ (U ⊔ r.range) → (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (hγ : ∀ t, (γ t : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ (U ⊔ r.range)) = t)
    (c : G × G → Rep.res r (Rep.coind U.subtype (Rep.trivial k ↥U V)))
    (hc : c ∈ groupCohomology.levelCocycles₂ r (Rep.res r (Rep.coind U.subtype (Rep.trivial k ↥U V))))
    (h : ∀ t, (fun d : ↥(U.comap r) × ↥(U.comap r) =>
        ((c ((d.1 : G), (d.2 : G)) : Rep.coind U.subtype (Rep.trivial k ↥U V)) :
          (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → V) (γ t))
      ∈ groupCohomology.levelCoboundaries₂ (r.comp (U.comap r).subtype) (Rep.trivial k ↥(U.comap r) V)) :
    c ∈ groupCohomology.levelCoboundaries₂ r (Rep.res r (Rep.coind U.subtype (Rep.trivial k ↥U V))) :=
  P2MShMInj.main r U hU γ hγ c hc h

end S_groupCohomology_res_coind_mem_levelCoboundaries2_of_forall_apply_mem_levelCoboundaries2
end P2MW
export P2MW.S_groupCohomology_res_coind_mem_levelCoboundaries2_of_forall_apply_mem_levelCoboundaries2 (solution)
