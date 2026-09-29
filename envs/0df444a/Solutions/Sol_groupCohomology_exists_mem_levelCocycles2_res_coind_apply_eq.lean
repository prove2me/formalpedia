-- Prove2me | solution 1 for groupCohomology.exists_mem_levelCocycles2_res_coind_apply_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/bb625b88-ff46-5192-b5b4-9f306d3b220c

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_ContinuousH2Map
import Definitions.Def_GroupCohomology_LevelSubgroup
import Theorems.Thm_Rep_exists_res_coind_linearEquiv_coind_comap
import Theorems.Thm_groupCohomology_exists_coind_mem_levelCocycles2_eval_one_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_exists_mem_levelCocycles2_res_coind_apply_eq

set_option autoImplicit false

universe u

open CategoryTheory groupCohomology

noncomputable section

namespace P2MShMSurj

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

variable (b : T r U → ↥(U.comap r) × ↥(U.comap r) → V)

def bigB : ↥(U.comap r) × ↥(U.comap r) → (T r U → V) := fun dd t => b t dd

omit [AddCommGroup V] [Module k V] in
lemma bigB_apply (dd : ↥(U.comap r) × ↥(U.comap r)) (t : T r U) : bigB r U b dd t = b t dd := rfl

lemma bigB_mem_cocycles₂ (hb : ∀ t, b t ∈ levelCocycles₂ (r.comp (U.comap r).subtype) (Rep.trivial k ↥(U.comap r) V)) :
    bigB r U b ∈ cocycles₂ (Rep.trivial k ↥(U.comap r) (T r U → V)) := by
  rw [mem_cocycles₂_iff]
  intro g h j
  funext t
  have := (mem_cocycles₂_iff _).1 (hb t).1 g h j
  rw [Rep.trivial_ρ_apply] at this
  rw [Rep.trivial_ρ_apply]
  simpa [bigB] using this

lemma bigB_isLevelConstant [Finite (T r U)]
    (hb : ∀ t, b t ∈ levelCocycles₂ (r.comp (U.comap r).subtype) (Rep.trivial k ↥(U.comap r) V)) :
    IsLevelConstant₂ (r.comp (U.comap r).subtype) (bigB r U b) := by
  choose F hF hc using fun t => (hb t).2
  haveI : ∀ t, FiniteDimensional ℚ (F t) := hF
  refine ⟨⨆ t, F t, IntermediateField.finiteDimensional_iSup_of_finite, fun g g' s s' hs hs' => ?_⟩
  funext t
  exact hc t g g' s s' (IntermediateField.fixingSubgroup_antitone (le_iSup F t) hs)
    (IntermediateField.fixingSubgroup_antitone (le_iSup F t) hs')

lemma symm_equivariant (e : P (k := k) (V := V) r U ≃ₗ[k] Q (k := k) (V := V) r U)
    (he : ∀ (g : G) (f : P (k := k) (V := V) r U), e ((P r U).ρ g f) = (Q r U).ρ g (e f))
    (g : G) (q : Q (k := k) (V := V) r U) :
    e.symm ((Q r U).ρ ((MonoidHom.id G) g) q) = (P r U).ρ g (e.symm q) := by
  apply e.injective
  rw [LinearEquiv.apply_symm_apply, he, LinearEquiv.apply_symm_apply, MonoidHom.id_apply]

theorem main [U.Normal]
    (hU : ∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧ F₀.fixingSubgroup ≤ U)
    (γ : T r U → Γ) (hγ : ∀ t, (γ t : T r U) = t)
    (hb : ∀ t, b t ∈ levelCocycles₂ (r.comp (U.comap r).subtype) (Rep.trivial k ↥(U.comap r) V)) :
    ∃ c : G × G → P (k := k) (V := V) r U, c ∈ levelCocycles₂ r (P r U) ∧
      ∀ (t : T r U) (d d' : ↥(U.comap r)),
        ((c ((d : G), (d' : G)) : Rep.coind U.subtype (Rep.trivial k ↥U V)) : Γ → V) (γ t) = b t (d, d') := by
  haveI : Finite (T r U) := finite_T r U hU
  have hB : bigB r U b ∈ levelCocycles₂ (r.comp (U.comap r).subtype) (Rep.trivial k ↥(U.comap r) (T r U → V)) :=
    ⟨bigB_mem_cocycles₂ r U b hb, bigB_isLevelConstant r U b hb⟩
  have hS : ∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧
      F₀.fixingSubgroup.comap r ≤ U.comap r := by
    obtain ⟨F₀, hF₀, hle⟩ := hU
    exact ⟨F₀, hF₀, Subgroup.comap_mono hle⟩
  obtain ⟨C, hC, hC1⟩ := groupCohomology.exists_coind_mem_levelCocycles2_eval_one_eq r (U.comap r) hS
    (Rep.trivial k ↥(U.comap r) (T r U → V)) (bigB r U b) hB
  obtain ⟨e, he, hef⟩ := Rep.exists_res_coind_linearEquiv_coind_comap (k := k) (V := V) r U γ hγ
  have hz : cochainsPullPush₂ (A := Q r U) (B := P r U) (MonoidHom.id G) e.symm.toLinearMap C ∈
      levelCocycles₂ r (P r U) :=
    cochainsPullPush₂_mem_levelCocycles₂ (rH := r) (rG := r) (A := Q r U) (B := P r U) (MonoidHom.id G)
      (fun _ => rfl) e.symm.toLinearMap (symm_equivariant r U e he) hC
  refine ⟨cochainsPullPush₂ (A := Q r U) (B := P r U) (MonoidHom.id G) e.symm.toLinearMap C, hz, fun t d d' => ?_⟩
  rw [cochainsPullPush₂_apply, MonoidHom.id_apply, MonoidHom.id_apply, LinearEquiv.coe_toLinearMap]
  have key := hef (e.symm (C ((d : G), (d' : G)))) 1 t
  rw [LinearEquiv.apply_symm_apply, map_one, mul_one, hC1, bigB_apply] at key
  exact key.symm

end P2MShMSurj

end

theorem solution {k : Type u} [CommRing k] {V : Type u} [AddCommGroup V] [Module k V]
    {G : Type u} [Group G] (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (U : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) [U.Normal]
    (hU : ∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧ F₀.fixingSubgroup ≤ U)
    (γ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ (U ⊔ r.range) → (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (hγ : ∀ t, (γ t : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ (U ⊔ r.range)) = t)
    (b : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ (U ⊔ r.range) → ↥(U.comap r) × ↥(U.comap r) → V)
    (hb : ∀ t, b t ∈ groupCohomology.levelCocycles₂ (r.comp (U.comap r).subtype) (Rep.trivial k ↥(U.comap r) V)) :
    ∃ c : G × G → Rep.res r (Rep.coind U.subtype (Rep.trivial k ↥U V)),
      c ∈ groupCohomology.levelCocycles₂ r (Rep.res r (Rep.coind U.subtype (Rep.trivial k ↥U V))) ∧
      ∀ (t : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ (U ⊔ r.range)) (d d' : ↥(U.comap r)),
        ((c ((d : G), (d' : G)) : Rep.coind U.subtype (Rep.trivial k ↥U V)) :
          (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → V) (γ t) = b t (d, d') :=
  P2MShMSurj.main r U b hU γ hγ hb

end S_groupCohomology_exists_mem_levelCocycles2_res_coind_apply_eq
end P2MW
export P2MW.S_groupCohomology_exists_mem_levelCocycles2_res_coind_apply_eq (solution)
