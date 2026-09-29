-- Prove2me | solution 1 for groupCohomology.exists_level_sylow_of_isOpen
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/d37c2306-a854-597e-bf0c-293f3ea0a0e2

import Mathlib
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_ContinuousH2Map
import Definitions.Def_GroupCohomology_ContinuousH1
import Definitions.Def_GroupCohomology_CupProduct
import Definitions.Def_GroupCohomology_ContinuousDuality
import Definitions.Def_GroupCohomology_Selmer
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Theorems.Thm_ExtCitation_exists_padicLevel_fixingSubgroup_le_of_smooth
import Theorems.Thm_groupCohomology_exists_level_ofChar_cycloChar_comp
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_exists_level_sylow_of_isOpen
p2m_attr_erase "instance" "groupCohomology.normal_comap_fixingSubgroup groupCohomology.finiteIndex_comap_fixingSubgroup"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
open CategoryTheory Module groupCohomology ExtCitation

set_option maxHeartbeats 3200000 in
theorem solution
    {p : ℕ} [Fact p.Prime] (q : Nat.Primes)
    (S : Subgroup (primeLocalGaloisGroup q))
    (hS : ∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧
      F₀.fixingSubgroup.comap (primeLocalToGlobal q) ≤ S)
    (M : Rep.{0} (ZMod p) S) [FiniteDimensional (ZMod p) M]
    (hsm : ∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s : S, ((primeLocalToGlobal q).comp S.subtype) s ∈ F.fixingSubgroup → M.ρ s m = m) :
    ∃ (U T : Subgroup (primeLocalGaloisGroup q)),
      T ≤ S ∧
      (∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧
        F₀.fixingSubgroup.comap (primeLocalToGlobal q) ≤ T) ∧
      (T.subgroupOf S).FiniteIndex ∧ IsUnit (((T.subgroupOf S).index : ℕ) : ZMod p) ∧
      (∀ s : primeLocalGaloisGroup q, s ∈ T → ∃ n : ℕ, s ^ (p ^ n) ∈ U) ∧
      (∀ s : S, (s : primeLocalGaloisGroup q) ∈ U → ∀ m : M, M.ρ s m = m) ∧
      (∀ u : primeLocalGaloisGroup q, u ∈ U → (cycloChar p) (primeLocalToGlobal q u) = 1) := by
  classical
  haveI : Fact (q : ℕ).Prime := ⟨q.2⟩

  have exists_isGalois_ge : ∀ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F →
      ∃ F' : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F' ∧ IsGalois ℚ F' ∧ F ≤ F' := by
    intro F hF
    haveI := hF
    haveI : Normal ℚ (AlgebraicClosure ℚ) := by
      convert @IsAlgClosure.normal ℚ (AlgebraicClosure ℚ) _ _ (AlgebraicClosure.instAlgebra ℚ) inferInstance <;>
        first | with_reducible_and_instances rfl | exact Subsingleton.elim _ _
    let L : IntermediateField ℚ (AlgebraicClosure ℚ) := IntermediateField.normalClosure ℚ F (AlgebraicClosure ℚ)
    haveI : FiniteDimensional ℚ L := normalClosure.is_finiteDimensional ℚ F (AlgebraicClosure ℚ)
    haveI : Normal ℚ L := normalClosure.normal ℚ F (AlgebraicClosure ℚ)
    haveI : IsGalois ℚ L := ⟨⟩
    exact ⟨L, inferInstance, inferInstance, IntermediateField.le_normalClosure F⟩

  obtain ⟨K₁, hK₁, -, ⟨E₁, hE₁, hE₁K⟩, hfi₁, hK₁S, hK₁M⟩ :=
    ExtCitation.exists_padicLevel_fixingSubgroup_le_of_smooth p q S hS M hsm
  obtain ⟨Fχ, hFχ, hχ⟩ := groupCohomology.exists_level_ofChar_cycloChar_comp (p := p) (primeLocalToGlobal q) (1 : ZMod p)
  let Nχ : Rep (ZMod p) S := Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))
  have hsmχ : ∀ n : Nχ, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s : S, ((primeLocalToGlobal q).comp S.subtype) s ∈ F.fixingSubgroup → Nχ.ρ s n = n := by
    intro n
    refine ⟨Fχ, hFχ, fun s hs => ?_⟩
    have h1 : (((cycloChar p).comp (primeLocalToGlobal q) (s : primeLocalGaloisGroup q) : (ZMod p)ˣ) : ZMod p) * 1 = 1 :=
      hχ (s : primeLocalGaloisGroup q) hs
    show (((cycloChar p).comp (primeLocalToGlobal q) (s : primeLocalGaloisGroup q) : (ZMod p)ˣ) : ZMod p) * n = n
    rw [mul_one] at h1
    rw [h1, one_mul]
  obtain ⟨K₂, hK₂, -, ⟨E₂, hE₂, hE₂K⟩, hfi₂, hK₂S, hK₂χ⟩ :=
    ExtCitation.exists_padicLevel_fixingSubgroup_le_of_smooth p q S hS Nχ hsmχ
  haveI := hfi₁; haveI := hfi₂; haveI := hE₁; haveI := hE₂

  let U : Subgroup (primeLocalGaloisGroup q) :=
    (K₁.fixingSubgroup : Subgroup (primeLocalGaloisGroup q)) ⊓ (K₂.fixingSubgroup : Subgroup (primeLocalGaloisGroup q))
  have hUS : U ≤ S := fun s hs => hK₁S s hs.1
  haveI : Finite (primeLocalGaloisGroup q ⧸ (K₁.fixingSubgroup : Subgroup (primeLocalGaloisGroup q))) :=
    @Subgroup.finite_quotient_of_finiteIndex (primeLocalGaloisGroup q) _ _ hfi₁
  haveI : Finite (primeLocalGaloisGroup q ⧸ (K₂.fixingSubgroup : Subgroup (primeLocalGaloisGroup q))) :=
    @Subgroup.finite_quotient_of_finiteIndex (primeLocalGaloisGroup q) _ _ hfi₂
  haveI hUfi : U.FiniteIndex :=
    ⟨Subgroup.index_inf_ne_zero
      (Subgroup.index_ne_zero_of_finite (H := (K₁.fixingSubgroup : Subgroup (primeLocalGaloisGroup q))))
      (Subgroup.index_ne_zero_of_finite (H := (K₂.fixingSubgroup : Subgroup (primeLocalGaloisGroup q))))⟩
  obtain ⟨F, hF, hFG, hEF⟩ := exists_isGalois_ge (E₁ ⊔ E₂) (IntermediateField.finiteDimensional_sup E₁ E₂)
  haveI := hF; haveI := hFG
  have hFU : F.fixingSubgroup.comap (primeLocalToGlobal q) ≤ U := fun s hs =>
    ⟨hE₁K (IntermediateField.fixingSubgroup_antitone (le_sup_left.trans hEF) hs),
     hE₂K (IntermediateField.fixingSubgroup_antitone (le_sup_right.trans hEF) hs)⟩

  let U' : Subgroup S := U.subgroupOf S
  let L : Subgroup S := (F.fixingSubgroup.comap (primeLocalToGlobal q)).subgroupOf S
  haveI : Normal ℚ (AlgebraicClosure ℚ) := by
    convert @IsAlgClosure.normal ℚ (AlgebraicClosure ℚ) _ _ (AlgebraicClosure.instAlgebra ℚ) inferInstance <;>
      first | with_reducible_and_instances rfl | exact Subsingleton.elim _ _
  haveI hGal : IsGalois ℚ (AlgebraicClosure ℚ) := ⟨⟩
  haveI : (F.fixingSubgroup.comap (primeLocalToGlobal q)).Normal := by
    haveI : F.fixingSubgroup.Normal := (InfiniteGalois.normal_iff_isGalois F).2 hFG
    exact Subgroup.normal_comap _
  haveI hLn : L.Normal := Subgroup.normal_subgroupOf
  have hLU' : L ≤ U' := fun s hs => hFU hs
  haveI : U'.FiniteIndex := inferInstance
  let V : Subgroup S := U'.normalCore
  haveI : V.Normal := inferInstance
  haveI : V.FiniteIndex := Subgroup.finiteIndex_normalCore U'
  have hLV : L ≤ V := Subgroup.normal_le_normalCore.2 hLU'
  have hVU' : V ≤ U' := Subgroup.normalCore_le U'

  haveI : Finite (S ⧸ V) := Subgroup.finite_quotient_of_finiteIndex
  let P : Sylow p (S ⧸ V) := default
  let T' : Subgroup S := (P : Subgroup (S ⧸ V)).comap (QuotientGroup.mk' V)
  have hVT' : V ≤ T' := fun s hs => by
    show (QuotientGroup.mk' V s) ∈ (P : Subgroup (S ⧸ V))
    have h1 : QuotientGroup.mk' V s = 1 := (QuotientGroup.eq_one_iff s).2 hs
    rw [h1]; exact one_mem _
  let T : Subgroup (primeLocalGaloisGroup q) := T'.map S.subtype
  have hTT' : T.subgroupOf S = T' := Subgroup.comap_map_eq_self_of_injective Subtype.val_injective T'
  haveI hT'fi : T'.FiniteIndex := Subgroup.finiteIndex_of_le hVT'
  refine ⟨U, T, Subgroup.map_subtype_le T', ⟨F, hF, fun s hs => ?_⟩, by rw [hTT']; infer_instance, ?_, ?_, ?_, ?_⟩
  ·
    have hsS : s ∈ S := hUS (hFU hs)
    exact ⟨⟨s, hsS⟩, hVT' (hLV (show (⟨s, hsS⟩ : S) ∈ L from hs)), rfl⟩
  ·
    rw [hTT']
    have hidx : T'.index = (P : Subgroup (S ⧸ V)).index :=
      Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective V)
    haveI : (P : Subgroup (S ⧸ V)).FiniteIndex := inferInstance
    have hnd : ¬ p ∣ T'.index := by rw [hidx]; exact P.not_dvd_index
    rw [isUnit_iff_ne_zero, Ne, CharP.cast_eq_zero_iff (ZMod p) p]
    exact hnd
  ·
    rintro s ⟨s', hs', rfl⟩
    obtain ⟨n, hn⟩ := P.isPGroup' ⟨QuotientGroup.mk' V s', hs'⟩
    refine ⟨n, ?_⟩
    have h1 : QuotientGroup.mk' V (s' ^ p ^ n) = 1 := by
      rw [map_pow]; exact congrArg Subtype.val hn
    have h2 : s' ^ p ^ n ∈ V := (QuotientGroup.eq_one_iff _).1 h1
    exact hVU' h2
  ·
    intro s hs m
    exact hK₁M s hs.1 m
  ·
    intro u hu
    have := hK₂χ ⟨u, hUS hu⟩ hu.2 (1 : ZMod p)
    have h1 : (((cycloChar p).comp (primeLocalToGlobal q) u : (ZMod p)ˣ) : ZMod p) * 1 = 1 := this
    rw [mul_one] at h1
    exact Units.val_eq_one.1 h1

end S_groupCohomology_exists_level_sylow_of_isOpen
end P2MW
export P2MW.S_groupCohomology_exists_level_sylow_of_isOpen (solution)
