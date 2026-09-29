-- Prove2me | solution 1 for groupCohomology.eq_zero_of_forall_continuousH2Map_primeLocal_eq_zero_pPrimary_continuousH2Sr_sUnitsMax
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/17962c37-ad15-5041-b8f5-5db6379b0659

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_NumberField_SelmerRepModP
import Definitions.Def_NumberField_SUnitsMax
import Definitions.Def_GroupCohomology_LevelSubgroup
import Definitions.Def_NumberField_SIdeleModule
import Definitions.Def_GroupCohomology_Corestriction2
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelInflation
import Definitions.Def_FieldTheory_RatAlgClosureGalois
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_GroupCohomology_RepPi
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_NumberField_FiniteSIdeleModule
import Definitions.Def_NumberField_PlaceAbove
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_SIdeleClassModule
import Definitions.Def_NumberField_SUnitsModule
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_ContinuousH2Map
import Theorems.Thm_groupCohomology_exists_continuousH2SrInflation_eq
import Theorems.Thm_groupCohomology_continuousH2SrInflation_H2pi_eq_of_le
import Theorems.Thm_groupCohomology_Cores_cores_map_res_eq_index_smul
import Theorems.Thm_NumberField_LevelArith_exists_addEquiv_quotientToInvariants_sUnitsMaxRep_sUnitsRep
import Theorems.Thm_IntermediateField_exists_normal_isUnramifiedOutside_of_le
import Theorems.Thm_NumberField_LevelArith_sUnitsMaxRep_smooth_and_divisible
import Theorems.Thm_NumberField_LevelArith_exists_level_coboundary_of_isPGroup_of_map_diag_H2pi_eq_zero_sUnitsMaxRep
import Theorems.Thm_NumberField_PlaceDecomp_exists_fundamentalClass_units_adicCompletion
import Theorems.Thm_NumberField_PlaceDecomp_exists_restrict_decomp_surjective_of_tower
import Theorems.Thm_NumberField_PlaceDecomp_forall_smul_eq_iff_mem_range_adicCompletionSemialgHom
import Theorems.Thm_NumberField_ramificationIdx_under_eq_one_of_forall_liesOverPrime_inertiaSubgroupIn_le_fixingSubgroup
import Theorems.Thm_groupCohomology_H2inf_injective_of_subsingleton_H1_res
import Theorems.Thm_groupCohomology_coindIso_hom_eq_map_subtype_comp_map_eval_one
import Theorems.Thm_NumberField_SIdele_bijective_groupCohomology_localCoordinates_of_ramificationIdx_eq_one
import Theorems.Thm_NumberField_LevelArith_sUnitsMaxStable_eq_sUnitsMax
import Theorems.Thm_NumberField_existsUnique_heightOneSpectrum_forall_map_mem_iff_valuation_le_one
import Theorems.Thm_ValuationSubring_decompositionSubgroup_padicPlace_le_closure_range_localGaloisToGlobal
import Theorems.Thm_ValuationSubring_map_restrictNormalHom_decompositionSubgroup_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_eq_zero_of_forall_continuousH2Map_primeLocal_eq_zero_pPrimary_continuousH2Sr_sUnitsMax
p2m_attr_erase "instance" "FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion NumberField.AdelicHaar.locallyCompactSpace_adeleRing NumberField.AdelicHaar.finite_residueField_adicCompletionIntegers NumberField.AdelicHaar.locallyCompactSpace_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_finiteAdeleRing NumberField.AdelicHaar.compactSpace_adicCompletionIntegers NumberField.AdelicHaar.t2Space_finiteAdeleRing NumberField.AdelicHaar.t2Space_matrix_adeleRing NumberField.AdelicHaar.t2Space_adeleRing NumberField.AdelicHaar.fact_isOpen_adicCompletionIntegers NumberField.AdelicHaar.t2Space_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_matrix_adeleRing NumberField.AdelicHaar.t2Space_infiniteAdeleRing NumberField.AdelicHaar.properSpace_adicCompletion M4aHerbrand.Bridge.instT2SpaceAdeleRing M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite Deep.NTSupply.instNormalRayClassSubgroup instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace"
p2m_attr_erase "instance" "NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal"
p2m_attr_erase "simp" "M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq M4aHerbrand.Bridge.finiteConorm_apply M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"
p2m_attr_erase "simp" "RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk M4aHerbrand.IdeleGaloisDescent.classAct_mk Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq"
p2m_attr_erase "simp" "LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent IsLocalRing.principalUnits_zero"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Module CategoryTheory.Limits CategoryTheory.MonoidalCategory.Limits groupCohomology P2MW.S_groupCohomology_eq_zero_of_forall_continuousH2Map_primeLocal_eq_zero_pPrimary_continuousH2Sr_sUnitsMax.groupCohomology ExtCitation NumberField.LevelArith"
open scoped Classical NumberField.LevelArith TensorProduct Pointwise

namespace PPrimarySylowReduction

private theorem eq_zero_of_pow_nsmul_eq_zero_of_coprime_nsmul_eq_zero {M : Type*} [AddCommGroup M] {p : ℕ}
    {x : M} (hx : ∃ k : ℕ, p ^ k • x = 0) {n : ℕ} (hn : n.Coprime p) (h : n • x = 0) : x = 0 := by
  obtain ⟨k, hk⟩ := hx
  obtain ⟨a, b, hab⟩ : IsCoprime (n : ℤ) (((p ^ k : ℕ) : ℤ)) :=
    Nat.isCoprime_iff_coprime.mpr (Nat.Coprime.pow_right k hn)
  calc x = (a * (n : ℤ) + b * ((p ^ k : ℕ) : ℤ)) • x := by rw [hab, one_zsmul]
    _ = a • ((n : ℤ) • x) + b • (((p ^ k : ℕ) : ℤ) • x) := by rw [add_zsmul, mul_zsmul, mul_zsmul]
    _ = 0 := by rw [natCast_zsmul, natCast_zsmul, h, hk, smul_zero, smul_zero, add_zero]

private theorem exists_pow_nsmul_eq_zero_of_mem_torsion'_powers {M : Type*} [AddCommMonoid M] [Module ℤ M]
    {p : ℕ} {x : M} (hx : x ∈ Submodule.torsion' ℤ M (Submonoid.powers (p : ℤ))) :
    ∃ k : ℕ, p ^ k • x = 0 := by
  rw [Submodule.mem_torsion'_iff] at hx
  obtain ⟨⟨s, k, rfl⟩, hs⟩ := hx
  refine ⟨k, ?_⟩
  have hs' : ((p : ℤ) ^ k) • x = 0 := hs
  rw [← Nat.cast_smul_eq_nsmul ℤ (p ^ k) x, Nat.cast_pow]
  exact hs'

end PPrimarySylowReduction

namespace HasseSylowLevel

open IntermediateField

private theorem exists_sylowField (p : ℕ) [Fact p.Prime] (L F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLF : L ≤ F)
    [FiniteDimensional ℚ ↥F] [Normal ℚ ↥F] :
    ∃ L' : IntermediateField ℚ (AlgebraicClosure ℚ), L ≤ L' ∧ L' ≤ F ∧
      (L'.fixingSubgroup.relIndex L.fixingSubgroup).Coprime p ∧
      IsPGroup p (↥L'.fixingSubgroup ⧸ F.fixingSubgroup.comap L'.fixingSubgroup.subtype) := by
  classical
  have hFL : F.fixingSubgroup ≤ L.fixingSubgroup := IntermediateField.fixingSubgroup_antitone hLF
  haveI : Finite ((AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ F.fixingSubgroup) :=
    Subgroup.quotient_finite_of_isOpen F.fixingSubgroup F.fixingSubgroup_isOpen
  haveI : F.fixingSubgroup.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient

  haveI : (F.fixingSubgroup.comap L.fixingSubgroup.subtype).FiniteIndex :=
    Subgroup.instFiniteIndex_subgroupOf F.fixingSubgroup L.fixingSubgroup
  obtain ⟨P⟩ :
      Nonempty (Sylow p (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype)) := inferInstance

  obtain ⟨P₁, hP₁⟩ : ∃ P₁ : Subgroup ↥L.fixingSubgroup,
      P₁ = (P : Subgroup _).comap (QuotientGroup.mk' (F.fixingSubgroup.comap L.fixingSubgroup.subtype)) := ⟨_, rfl⟩
  obtain ⟨P', hP'⟩ : ∃ P' : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
      P' = P₁.map L.fixingSubgroup.subtype := ⟨_, rfl⟩
  have hP'L : P' ≤ L.fixingSubgroup := by
    rw [hP']
    exact Subgroup.map_subtype_le P₁
  have hFP' : F.fixingSubgroup ≤ P' := by
    rw [hP']
    intro σ hσ
    refine Subgroup.mem_map.2 ⟨⟨σ, hFL hσ⟩, ?_, rfl⟩
    rw [hP₁, Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff _).2
      (show (⟨σ, hFL hσ⟩ : ↥L.fixingSubgroup) ∈ F.fixingSubgroup.comap L.fixingSubgroup.subtype from hσ)]
    exact one_mem _
  have hP'open : IsOpen (P' : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) :=
    Subgroup.isOpen_mono hFP' F.fixingSubgroup_isOpen

  have hfix : (fixedField P').fixingSubgroup = P' :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨P', Subgroup.isClosed_of_isOpen P' hP'open⟩
  refine ⟨fixedField P', (IntermediateField.le_iff_le P' L).2 hP'L, ?_, ?_, ?_⟩
  ·
    calc fixedField P' ≤ fixedField F.fixingSubgroup := IntermediateField.fixedField_antitone hFP'
      _ = F := InfiniteGalois.fixedField_fixingSubgroup F
  ·
    rw [hfix, Subgroup.relIndex, ← Subgroup.comap_subtype, hP',
      Subgroup.comap_map_eq_self_of_injective L.fixingSubgroup.subtype_injective P₁, hP₁,
      Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective _)]
    exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 (Sylow.not_dvd_index P))
  ·
    have hle : (fixedField P').fixingSubgroup ≤ L.fixingSubgroup := hfix.le.trans hP'L
    obtain ⟨ψ, hψdef⟩ : ∃ ψ : ↥(fixedField P').fixingSubgroup →*
        ↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype,
        ψ = (QuotientGroup.mk' _).comp (Subgroup.inclusion hle) := ⟨_, rfl⟩
    have hψ : ψ.range ≤ (P : Subgroup _) := by
      rintro _ ⟨σ, rfl⟩
      have hmem : (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ P₁.map L.fixingSubgroup.subtype := by
        rw [← hP']
        exact hfix.le σ.2
      obtain ⟨τ, hτ, hτσ⟩ := Subgroup.mem_map.1 hmem
      have hτ' : τ = Subgroup.inclusion hle σ := Subtype.ext hτσ
      rw [hP₁, Subgroup.mem_comap] at hτ
      rw [hψdef, MonoidHom.comp_apply, ← hτ']
      exact hτ
    have hker : F.fixingSubgroup.comap (fixedField P').fixingSubgroup.subtype = ψ.rangeRestrict.ker := by
      ext σ
      rw [MonoidHom.ker_rangeRestrict, MonoidHom.mem_ker, hψdef, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff, Subgroup.mem_comap, Subgroup.mem_comap]
      exact Iff.rfl
    have hP : IsPGroup p ↥ψ.range :=
      P.isPGroup'.of_injective (Subgroup.inclusion hψ) (Subgroup.inclusion_injective hψ)
    have hQ : IsPGroup p (↥(fixedField P').fixingSubgroup ⧸ ψ.rangeRestrict.ker) :=
      hP.of_injective (QuotientGroup.kerLift ψ.rangeRestrict) (QuotientGroup.kerLift_injective _)
    exact hQ.of_injective (QuotientGroup.quotientMulEquivOfEq hker).toMonoidHom
      (QuotientGroup.quotientMulEquivOfEq hker).injective

private theorem index_map_mk'_eq_relIndex (L L' F' : IntermediateField ℚ (AlgebraicClosure ℚ)) (hL'F' : L' ≤ F')
    [Normal ℚ ↥F'] :
    ((L'.fixingSubgroup.subgroupOf L.fixingSubgroup).map
        (QuotientGroup.mk' (F'.fixingSubgroup.comap L.fixingSubgroup.subtype))).index =
      L'.fixingSubgroup.relIndex L.fixingSubgroup :=
  Subgroup.index_map_eq _ (QuotientGroup.mk'_surjective _) (by
    rw [QuotientGroup.ker_mk']
    exact Subgroup.comap_mono (IntermediateField.fixingSubgroup_antitone hL'F'))

end HasseSylowLevel

section

p2m_open "IsDedekindDomain NumberField P2MW.S_groupCohomology_eq_zero_of_forall_continuousH2Map_primeLocal_eq_zero_pPrimary_continuousH2Sr_sUnitsMax.NumberField CategoryTheory"
p2m_open_scoped "NumberField.PlaceDecomp P2MW.S_groupCohomology_eq_zero_of_forall_continuousH2Map_primeLocal_eq_zero_pPrimary_continuousH2Sr_sUnitsMax.NumberField.PlaceDecomp NumberField.InfPlaceDecomp"

namespace CrepdCoord

private theorem eq_zero_of_forall_localCoordinate_eq_zero (E K : Type) [Field E] [NumberField E]
    [Field K] [NumberField K] [Algebra E K] [IsGalois E K] (S : Finset (HeightOneSpectrum (𝓞 E)))
    (hbij :
      Function.Bijective (fun x : groupCohomology (NumberField.SIdele.obj E K S) (1 + 1) =>
        ((fun v : {v // v ∈ S} =>
            (groupCohomology.map (MonoidHom.id (K ≃ₐ[E] K))
                (GroupCohomology.RepPi.proj (NumberField.SIdele.fibre E K S) (Sum.inl (Sum.inl v))) (1 + 1) ≫
              (groupCohomology.coindIso (NumberField.FiniteSIdele.localUnits E K v.1) (1 + 1)).hom).hom x),
         (fun v : InfinitePlace E =>
            (groupCohomology.map (MonoidHom.id (K ≃ₐ[E] K))
                (GroupCohomology.RepPi.proj (NumberField.SIdele.fibre E K S) (Sum.inr v)) (1 + 1) ≫
              (groupCohomology.coindIso
                (NumberField.InfPlaceDecomp.localUnits E K (NumberField.ArchIdele.above E K v)) (1 + 1)).hom).hom x))))
    (z : groupCohomology (NumberField.SIdele.obj E K S) 2)
    (hS : ∀ v : {v // v ∈ S},
      (groupCohomology.map (MonoidHom.id (K ≃ₐ[E] K))
          (GroupCohomology.RepPi.proj (NumberField.SIdele.fibre E K S) (Sum.inl (Sum.inl v))) 2 ≫
        (groupCohomology.coindIso (NumberField.FiniteSIdele.localUnits E K v.1) 2).hom).hom z = 0)
    (hinf : ∀ v : InfinitePlace E,
      (groupCohomology.map (MonoidHom.id (K ≃ₐ[E] K))
          (GroupCohomology.RepPi.proj (NumberField.SIdele.fibre E K S) (Sum.inr v)) 2 ≫
        (groupCohomology.coindIso (NumberField.InfPlaceDecomp.localUnits E K (NumberField.ArchIdele.above E K v))
          2).hom).hom z = 0) :
    z = 0 := by
  refine hbij.injective ?_
  refine Prod.ext (funext fun v => ?_) (funext fun v => ?_)
  · exact (hS v).trans (map_zero _).symm
  · exact (hinf v).trans (map_zero _).symm

end CrepdCoord
end

section

p2m_open "NumberField P2MW.S_groupCohomology_eq_zero_of_forall_continuousH2Map_primeLocal_eq_zero_pPrimary_continuousH2Sr_sUnitsMax.NumberField"

namespace CrepdArch

private theorem subsingleton_stabilizer_of_isPGroup {E K : Type} [Field E] [Field K]
    [Algebra E K] (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hG : IsPGroup p (K ≃ₐ[E] K))
    (w : InfinitePlace K) :
    Subsingleton (MulAction.stabilizer (K ≃ₐ[E] K) w) := by
  haveI : Fact p.Prime := ⟨hp⟩
  rcases (hG.to_subgroup (MulAction.stabilizer (K ≃ₐ[E] K) w)).card_eq_or_dvd with h1 | hdvd
  · exact (Nat.card_eq_one_iff_unique.mp h1).1
  · exfalso
    rcases InfinitePlace.nat_card_stabilizer_eq_one_or_two E w with h | h
    · rw [h] at hdvd
      exact hp.one_lt.ne' (Nat.dvd_one.mp hdvd)
    · rw [h] at hdvd
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hdvd)

private theorem subsingleton_stabilizer_of_sq_eq_neg_one {E K : Type} [Field E] [Field K]
    [Algebra E K] (hi : ∃ i : E, i ^ 2 = -1) (w : InfinitePlace K) :
    Subsingleton (MulAction.stabilizer (K ≃ₐ[E] K) w) := by
  have hunr : w.IsUnramified E := by
    rw [InfinitePlace.isUnramified_iff, ← InfinitePlace.not_isReal_iff_isComplex]
    right
    intro hreal
    obtain ⟨φ, hφ, -⟩ := hreal
    obtain ⟨i, hi⟩ := hi
    have hsq : (hφ.embedding i) ^ 2 = -1 := by
      rw [← map_pow, hi, map_neg, map_one]
    nlinarith [sq_nonneg (hφ.embedding i)]
  rw [hunr.stabilizer_eq_bot]
  infer_instance

private theorem eq_zero_of_subsingleton_group {k D : Type} [CommRing k] [Group D] [Subsingleton D]
    (A : Rep k D) (n : ℕ) (z : groupCohomology A (n + 1)) : z = 0 := by
  haveI := ModuleCat.subsingleton_of_isZero
    (isZero_groupCohomology_succ_of_subsingleton A n)
  exact Subsingleton.elim z 0

private theorem eq_zero_of_stabilizer {E K : Type} [Field E] [Field K] [Algebra E K]
    (p : ℕ) (hp : p.Prime) (h : p ≠ 2 ∧ IsPGroup p (K ≃ₐ[E] K) ∨ ∃ i : E, i ^ 2 = -1)
    (w : InfinitePlace K) {k : Type} [CommRing k]
    (A : Rep k (MulAction.stabilizer (K ≃ₐ[E] K) w)) (n : ℕ) (z : groupCohomology A (n + 1)) :
    z = 0 := by
  haveI : Subsingleton (MulAction.stabilizer (K ≃ₐ[E] K) w) := by
    rcases h with ⟨hp2, hG⟩ | hi
    · exact subsingleton_stabilizer_of_isPGroup p hp hp2 hG w
    · exact subsingleton_stabilizer_of_sq_eq_neg_one hi w
  exact eq_zero_of_subsingleton_group A n z

private theorem exists_sq_eq_neg_one_of_le {L L' : IntermediateField ℚ (AlgebraicClosure ℚ)}
    (hLL' : L ≤ L') (h4 : ∃ i ∈ L, i ^ 2 = -1) : ∃ i : ↥L', i ^ 2 = -1 := by
  obtain ⟨i, hi, hsq⟩ := h4
  exact ⟨⟨i, hLL' hi⟩, Subtype.ext (by simpa using hsq)⟩

private theorem eq_zero_of_localUnits (E K : Type) [Field E] [NumberField E] [Field K]
    [NumberField K] [Algebra E K] (p : ℕ) (hp : p.Prime)
    (h : p ≠ 2 ∧ IsPGroup p (K ≃ₐ[E] K) ∨ ∃ i : E, i ^ 2 = -1)
    (v : InfinitePlace E) (n : ℕ)
    (z : groupCohomology (InfPlaceDecomp.localUnits E K (ArchIdele.above E K v)) (n + 1)) : z = 0 :=
  eq_zero_of_stabilizer p hp h (ArchIdele.above E K v) (InfPlaceDecomp.localUnits E K _) n z

end CrepdArch
end

section

p2m_open "NumberField P2MW.S_groupCohomology_eq_zero_of_forall_continuousH2Map_primeLocal_eq_zero_pPrimary_continuousH2Sr_sUnitsMax.NumberField IsDedekindDomain"
open scoped NumberField.LevelArith

namespace LevelUnramified

private theorem exists_primes_cast_mem {K : Type*} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) :
    ∃ q : Nat.Primes, ((q : ℕ) : 𝓞 K) ∈ w.asIdeal := by
  haveI : Finite (𝓞 K ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot w.asIdeal w.ne_bot
  refine ⟨⟨ringChar (𝓞 K ⧸ w.asIdeal), CharP.prime_ringChar (𝓞 K ⧸ w.asIdeal)⟩, ?_⟩
  show ((ringChar (𝓞 K ⧸ w.asIdeal) : ℕ) : 𝓞 K) ∈ w.asIdeal
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact CharP.cast_eq_zero (𝓞 K ⧸ w.asIdeal) (ringChar (𝓞 K ⧸ w.asIdeal))

private theorem hunr_of_isUnramifiedOutside (S : Finset Nat.Primes)
    (L' F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hL'F : L' ≤ F) [FiniteDimensional ℚ L']
    [FiniteDimensional ℚ F] [Normal ℚ F] (hF : F.IsUnramifiedOutside S) :
    ∀ w : HeightOneSpectrum (𝓞 (LevelArith.levelField L' F hL'F)),
      w.under (𝓞 L') ∉ LevelArith.placesOverPrimesFinset L' S →
        (w.under (𝓞 L')).asIdeal.ramificationIdx' w.asIdeal = 1 := by
  haveI : IsGalois ℚ F := ⟨⟩
  intro w hw
  obtain ⟨q, hqw⟩ := exists_primes_cast_mem w

  have hqS : q ∉ S := by
    intro hq
    apply hw
    rw [LevelArith.mem_placesOverPrimesFinset]
    refine ⟨q, Finset.mem_coe.2 hq, ?_⟩
    show algebraMap (𝓞 L') (𝓞 (LevelArith.levelField L' F hL'F)) ((q : ℕ) : 𝓞 L') ∈ w.asIdeal
    rw [map_natCast]
    exact hqw

  let φL : L' →ₐ[ℚ] F :=
    ⟨(IntermediateField.inclusion hL'F).toRingHom, (IntermediateField.inclusion hL'F).toRingHom.map_rat_algebraMap⟩
  have key := NumberField.ramificationIdx_under_eq_one_of_forall_liesOverPrime_inertiaSubgroupIn_le_fixingSubgroup
    L' F φL q q.2 (fun P hP => hF.2 q hqS P hP)

  have hA : (φL.toRingHom.toAlgebra : Algebra L' (LevelArith.levelField L' F hL'F)) =
      (inferInstance : Algebra L' (LevelArith.levelField L' F hL'F)) :=
    Algebra.algebra_ext _ _ fun r => Subtype.ext rfl
  have key' := key w.asIdeal (inferInstance : w.asIdeal.IsMaximal) hqw
  rw [hA] at key'
  exact key'

end LevelUnramified
end

section

p2m_open "IsDedekindDomain NumberField P2MW.S_groupCohomology_eq_zero_of_forall_continuousH2Map_primeLocal_eq_zero_pPrimary_continuousH2Sr_sUnitsMax.NumberField CategoryTheory groupCohomology P2MW.S_groupCohomology_eq_zero_of_forall_continuousH2Map_primeLocal_eq_zero_pPrimary_continuousH2Sr_sUnitsMax.groupCohomology"
p2m_open_scoped "NumberField.PlaceDecomp P2MW.S_groupCohomology_eq_zero_of_forall_continuousH2Map_primeLocal_eq_zero_pPrimary_continuousH2Sr_sUnitsMax.NumberField.PlaceDecomp"

universe u

namespace groupCohomology
p2m_export "groupCohomology" "map_comp H2π mem_cocycles₂_def congr coindIso cocycles₂ cocycles₂.val_eq_coe d₁₂_hom_apply coe_mapCocycles₂ H2π_comp_map_apply map mem_cocycles₂_iff π mapCocycles₂ H2_induction_on δ H2π_eq_zero_iff H1 cochainsMap₂ IsLevelConstant₁ mem_levelCoboundaries₂_iff continuousH2π_eq_zero_iff coe_levelCocycles₂Map continuousH2Map continuousH2Map_continuousH2π continuousH2Sr continuousH2SrToContinuousH2 continuousH2SrToContinuousH2_mk comap_fixingSubgroup_antitone Cores.Transversal Cores.Transversal.nonempty continuousH2SrInflation continuousH2SrInflation_H2π exists_continuousH2SrInflation_eq continuousH2SrInflation_H2pi_eq_of_le Cores.cores_map_res_eq_index_smul H2inf_injective_of_subsingleton_H1_res coindIso_hom_eq_map_subtype_comp_map_eval_one"
p2m_open "groupCohomology"

private theorem H2π_quotientToInvariants_eq_zero_of_forall_eq_sub_add
    {k G : Type u} [CommRing k] [Group G] (A : Rep k G) (N : Subgroup G) [N.Normal]
    [Subsingleton (H1 (Rep.res N.subtype A))]
    (f : cocycles₂ (A.quotientToInvariants N)) (y : G → A)
    (hy : ∀ g h : G,
      ((f ((g : G ⧸ N), (h : G ⧸ N)) : A.quotientToInvariants N) : A) = A.ρ g (y h) - y (g * h) + y g) :
    H2π (A.quotientToInvariants N) f = 0 := by
  apply H2inf_injective_of_subsingleton_H1_res A N
  rw [map_zero, H2π_comp_map_apply, H2π_eq_zero_iff]
  refine ⟨y, ?_⟩
  funext gh
  obtain ⟨g, h⟩ := gh
  have := hy g h
  (first | exact this.symm | simpa [coe_mapCocycles₂, cochainsMap₂] using this.symm | (have h__ := this.symm; simp [coe_mapCocycles₂, cochainsMap₂] at h__; exact h__))

private theorem H2π_eq_zero_of_surjective_of_forall_eq_sub_add
    {k G D : Type u} [CommRing k] [Group G] [Group D] (r : G →* D) (hr : Function.Surjective r)
    (A : Rep k G) [Subsingleton (H1 (Rep.res r.ker.subtype A))]
    (B : Rep k D) (j : B →ₗ[k] A) (hj : Function.Injective j)
    (hjρ : ∀ (g : G) (b : B), j (B.ρ (r g) b) = A.ρ g (j b))
    (hjinv : ∀ a : A, (∀ n : G, n ∈ r.ker → A.ρ n a = a) → ∃ b : B, j b = a)
    (f : cocycles₂ B) (y : G → A)
    (hy : ∀ g h : G, j (f (r g, r h)) = A.ρ g (y h) - y (g * h) + y g) :
    H2π B f = 0 := by
  set N : Subgroup G := r.ker with hN
  let e : G ⧸ N ≃* D := QuotientGroup.quotientKerEquivOfSurjective r hr
  have he : ∀ g : G, e (g : G ⧸ N) = r g := fun g => QuotientGroup.kerLift_mk r g

  have hinv : ∀ b : B, j b ∈ Representation.invariants (A.ρ.comp N.subtype) := by
    intro b
    rw [Representation.mem_invariants]
    rintro ⟨n, hn⟩
    have h1 : r n = 1 := hn
    simpa [h1] using (hjρ n b).symm

  let F : (G ⧸ N) × (G ⧸ N) → A.quotientToInvariants N := fun x => ⟨j (f (e x.1, e x.2)), hinv _⟩
  have hFρ : ∀ (g : G) (s : A.quotientToInvariants N),
      (((A.quotientToInvariants N).ρ (g : G ⧸ N) s : A.quotientToInvariants N) : A) = A.ρ g (s : A) := fun _ _ => rfl
  have hFmem : F ∈ cocycles₂ (A.quotientToInvariants N) := by
    rw [mem_cocycles₂_iff]
    intro x z w
    induction x using QuotientGroup.induction_on with
    | H g =>
      apply Subtype.ext
      have hf := (mem_cocycles₂_iff (A := B) f).1 f.2 (r g) (e z) (e w)
      simp only [F, Submodule.coe_add, hFρ, map_mul, he]
      rw [← hjρ]
      simpa only [map_add] using congrArg j hf
  let Ft : cocycles₂ (A.quotientToInvariants N) := ⟨F, hFmem⟩
  have hFt : H2π (A.quotientToInvariants N) Ft = 0 := by
    apply H2π_quotientToInvariants_eq_zero_of_forall_eq_sub_add A N Ft y
    intro g h
    (first | exact hy g h | simpa [Ft, F, he] using hy g h | (have h__ := hy g h; simp [Ft, F, he] at h__; exact h__))
  rw [H2π_eq_zero_iff] at hFt
  obtain ⟨u, hu⟩ := hFt

  have hlift : ∀ d : D, ∃ b : B, j b = ((u (e.symm d) : A.quotientToInvariants N) : A) := by
    intro d
    apply hjinv
    intro n hn
    exact (Representation.mem_invariants _ _).1 (u (e.symm d)).2 ⟨n, hn⟩
  choose v hv using hlift
  rw [H2π_eq_zero_iff]
  refine ⟨v, ?_⟩
  funext dd
  obtain ⟨d₁, d₂⟩ := dd
  obtain ⟨g₁, rfl⟩ := hr d₁
  obtain ⟨g₂, rfl⟩ := hr d₂
  have hs₁ : e.symm (r g₁) = (g₁ : G ⧸ N) := e.symm_apply_eq.2 (he g₁).symm
  have hs₂ : e.symm (r g₂) = (g₂ : G ⧸ N) := e.symm_apply_eq.2 (he g₂).symm
  have hs₁₂ : e.symm (r g₁ * r g₂) = ((g₁ * g₂ : G) : G ⧸ N) := by
    rw [map_mul, hs₁, hs₂]; rfl
  apply hj
  have hu' := congrFun hu ((g₁ : G ⧸ N), (g₂ : G ⧸ N))
  have hu'' := congrArg (fun s : A.quotientToInvariants N => (s : A)) hu'
  simp only [d₁₂_hom_apply, Submodule.coe_add, Submodule.coe_sub, hFρ] at hu''
  simp only [d₁₂_hom_apply, map_add, map_sub, hjρ, hv, hs₁, hs₂, hs₁₂]
  exact hu''

end groupCohomology

namespace NumberField
p2m_export "NumberField" "place RingOfIntegers.coe_eq_zero_iff RingOfIntegers InfinitePlace.not_isReal_iff_isComplex InfinitePlace InfinitePlace.isUnramified_iff InfinitePlace.nat_card_stabilizer_eq_one_or_two LevelArith.levelField LevelArith.placesOverPrimesFinset LevelArith.mem_placesOverPrimesFinset SUnits.sUnitsRep SUnits.loc SUnits.val PlaceAbove.above PlaceAbove.comap_above PlaceDecomp.decomp SIdele.fibre SIdele.obj SIdele.diag SUnits.diagIn SUnits.diagIn_hom_apply_apply FiniteSIdele.D FiniteSIdele.localUnits InfPlaceDecomp.localUnits ArchIdele.above ramificationIdx_under_eq_one_of_forall_liesOverPrime_inertiaSubgroupIn_le_fixingSubgroup SIdele.bijective_groupCohomology_localCoordinates_of_ramificationIdx_eq_one existsUnique_heightOneSpectrum_forall_map_mem_iff_valuation_le_one"
namespace PlaceDecomp
p2m_export "NumberField.PlaceDecomp" "decomp actRingEquiv_apply actRingEquiv_coe smul_def coe_smul_units exists_fundamentalClass_units_adicCompletion exists_restrict_decomp_surjective_of_tower forall_smul_eq_iff_mem_range_adicCompletionSemialgHom"
p2m_open "NumberField.PlaceDecomp NumberField"

variable (E K K'' : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Field K''] [NumberField K'']
  [Algebra E K] [Algebra K K''] [Algebra E K''] [IsScalarTower E K K''] [IsGalois E K''] [IsGalois E K]
  (w'' : HeightOneSpectrum (𝓞 K''))

omit [NumberField E] [NumberField K] [IsGalois E K''] [IsGalois E K] in

private theorem smul_eq_smul_of_coe_eq (τ : decomp K K'' w'') (σ : decomp E K'' w'')
    (h : (σ : K'' ≃ₐ[E] K'') = AlgEquiv.restrictScalars E (τ : K'' ≃ₐ[K] K'')) (x : w''.adicCompletion K'') :
    τ • x = σ • x := by
  rw [smul_def, smul_def]
  apply IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext
  rw [actRingEquiv_apply, actRingEquiv_apply, h]
  rfl

private theorem H2π_eq_zero_of_exists_coboundary_above (p : HeightOneSpectrum (𝓞 K))
    (hp : HeightOneSpectrum.under (𝓞 K) w'' = p)
    (F : cocycles₂ (Rep.ofMulDistribMulAction (decomp E K p) (p.adicCompletion K)ˣ))
    (y : decomp E K'' w'' → Rep.ofMulDistribMulAction (decomp E K'' w'') (w''.adicCompletion K'')ˣ)
    (hy : ∀ (g h : decomp E K'' w'') (a b : decomp E K p),
      (a : K ≃ₐ[E] K) = AlgEquiv.restrictNormalHom K (g : K'' ≃ₐ[E] K'') →
      (b : K ≃ₐ[E] K) = AlgEquiv.restrictNormalHom K (h : K'' ≃ₐ[E] K'') →
      Additive.ofMul (Units.map (HeightOneSpectrum.Extension.adicCompletionSemialgHom K K''
          (⟨w'', hp⟩ : p.Extension (𝓞 K''))).toRingHom.toMonoidHom (Additive.toMul (F (a, b)))) =
        (Rep.ofMulDistribMulAction (decomp E K'' w'') (w''.adicCompletion K'')ˣ).ρ g (y h) - y (g * h) + y g) :
    H2π _ F = 0 := by
  subst hp
  obtain ⟨r, hr, hrcoe, -, hlift, hsemi⟩ := exists_restrict_decomp_surjective_of_tower E K K'' w''
  haveI : IsGalois K K'' := IsGalois.tower_top_of_isGalois E K K''
  set ι : (HeightOneSpectrum.under (𝓞 K) w'').adicCompletion K →+* w''.adicCompletion K'' :=
    (HeightOneSpectrum.Extension.adicCompletionSemialgHom K K''
      (⟨w'', rfl⟩ : (HeightOneSpectrum.under (𝓞 K) w'').Extension (𝓞 K''))).toRingHom with hιdef

  haveI : Subsingleton (H1 (Rep.res r.ker.subtype
      (Rep.ofMulDistribMulAction (decomp E K'' w'') (w''.adicCompletion K'')ˣ))) := by
    obtain ⟨-, hH1, -, -⟩ := exists_fundamentalClass_units_adicCompletion E K'' w''
    exact ModuleCat.subsingleton_of_isZero (hH1 r.ker)

  let j : Rep.ofMulDistribMulAction (decomp E K (HeightOneSpectrum.under (𝓞 K) w''))
        ((HeightOneSpectrum.under (𝓞 K) w'').adicCompletion K)ˣ →ₗ[ℤ]
      Rep.ofMulDistribMulAction (decomp E K'' w'') (w''.adicCompletion K'')ˣ :=
    (MonoidHom.toAdditive (Units.map ι.toMonoidHom)).toIntLinearMap
  have hj : Function.Injective j := fun u₁ u₂ h =>
    Additive.toMul.injective (Units.map_injective ι.injective (congrArg Additive.toMul h))
  refine groupCohomology.H2π_eq_zero_of_surjective_of_forall_eq_sub_add r hr _ _ j hj ?_ ?_ F y ?_
  · intro σ b
    apply Additive.toMul.injective
    apply Units.ext
    simp only [j, Rep.ofMulDistribMulAction_ρ_apply_apply, RingHom.toMonoidHom_eq_coe]
    exact hsemi σ _
  · intro a ha
    obtain ⟨z, hz⟩ := (forall_smul_eq_iff_mem_range_adicCompletionSemialgHom K K'' w''
        ((Additive.toMul a : (w''.adicCompletion K'')ˣ) : w''.adicCompletion K'')).1 (fun τ => by
      obtain ⟨σ, hσ, hσ1⟩ := hlift τ
      have h1 := ha σ hσ1
      have h2 := congrArg (fun t => ((Additive.toMul t : (w''.adicCompletion K'')ˣ) : w''.adicCompletion K'')) h1
      simp only [Rep.ofMulDistribMulAction_ρ_apply_apply, toMul_ofMul, coe_smul_units] at h2
      rw [smul_eq_smul_of_coe_eq E K K'' w'' τ σ hσ]
      exact h2)
    have hz0 : z ≠ 0 := by
      rintro rfl
      exact (Additive.toMul a).ne_zero (by simpa using hz.symm)
    refine ⟨Additive.ofMul (Units.mk0 z hz0), ?_⟩
    apply Additive.toMul.injective
    apply Units.ext
    (first | exact hz | simpa [j] using hz | (have h__ := hz; simp [j] at h__; exact h__))
  · intro g h
    exact hy g h (r g) (r h) (hrcoe g) (hrcoe h)

end NumberField.PlaceDecomp

namespace NumberField p2m_export "NumberField" "place RingOfIntegers.coe_eq_zero_iff RingOfIntegers InfinitePlace.not_isReal_iff_isComplex InfinitePlace InfinitePlace.isUnramified_iff InfinitePlace.nat_card_stabilizer_eq_one_or_two LevelArith.levelField LevelArith.placesOverPrimesFinset LevelArith.mem_placesOverPrimesFinset SUnits.sUnitsRep SUnits.loc SUnits.val PlaceAbove.above PlaceAbove.comap_above PlaceDecomp.decomp SIdele.fibre SIdele.obj SIdele.diag SUnits.diagIn SUnits.diagIn_hom_apply_apply FiniteSIdele.D FiniteSIdele.localUnits InfPlaceDecomp.localUnits ArchIdele.above ramificationIdx_under_eq_one_of_forall_liesOverPrime_inertiaSubgroupIn_le_fixingSubgroup SIdele.bijective_groupCohomology_localCoordinates_of_ramificationIdx_eq_one existsUnique_heightOneSpectrum_forall_map_mem_iff_valuation_le_one" namespace SIdele p2m_export "NumberField.SIdele" "fibre obj diag bijective_groupCohomology_localCoordinates_of_ramificationIdx_eq_one" end NumberField.SIdele
p2m_open_scoped "NumberField NumberField.SIdele" in

private theorem NumberField.SIdele.localCoordinate_map_diag_H2π_eq_zero_of_exists_layer
    (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K]
    (S : Finset (HeightOneSpectrum (𝓞 E))) (f : cocycles₂ (SUnits.sUnitsRep E K S)) (v : {v // v ∈ S})
    (hloc : ∃ (K'' : Type) (_ : Field K'') (_ : NumberField K'') (_ : Algebra E K'') (_ : Algebra K K'')
      (_ : IsScalarTower E K K'') (_ : IsGalois E K'') (w'' : HeightOneSpectrum (𝓞 K''))
      (_ : HeightOneSpectrum.under (𝓞 K) w'' = PlaceAbove.above E K v.1)
      (y : PlaceDecomp.decomp E K'' w'' →
        Rep.ofMulDistribMulAction (PlaceDecomp.decomp E K'' w'') (w''.adicCompletion K'')ˣ),
      ∀ g h : PlaceDecomp.decomp E K'' w'',
        Additive.ofMul (Units.map (algebraMap K'' (w''.adicCompletion K'')).toMonoidHom
            (Units.map (algebraMap K K'').toMonoidHom (SUnits.val E K S
              (f (AlgEquiv.restrictNormalHom K (g : K'' ≃ₐ[E] K''),
                  AlgEquiv.restrictNormalHom K (h : K'' ≃ₐ[E] K'')))))) =
          (Rep.ofMulDistribMulAction (PlaceDecomp.decomp E K'' w'') (w''.adicCompletion K'')ˣ).ρ g (y h) -
            y (g * h) + y g) :
    (groupCohomology.map (MonoidHom.id (K ≃ₐ[E] K))
        (GroupCohomology.RepPi.proj (NumberField.SIdele.fibre E K S) (Sum.inl (Sum.inl v))) 2 ≫
      (groupCohomology.coindIso (NumberField.FiniteSIdele.localUnits E K v.1) 2).hom).hom
      ((groupCohomology.map (MonoidHom.id (K ≃ₐ[E] K)) (NumberField.SIdele.diag E K S) 2).hom
        (H2π (SUnits.sUnitsRep E K S) f)) = 0 := by
  classical
  obtain ⟨K'', _, _, _, _, _, _, w'', hw'', y, hy⟩ := hloc

  let ev : Rep.res (FiniteSIdele.D E K v.1).subtype
      (Rep.coind (FiniteSIdele.D E K v.1).subtype (FiniteSIdele.localUnits E K v.1)) ⟶
        FiniteSIdele.localUnits E K v.1 :=
    (Rep.resCoindHomEquiv (FiniteSIdele.D E K v.1).subtype _ (FiniteSIdele.localUnits E K v.1)).symm (𝟙 _)
  have hev : ∀ x, ev.hom x = (x : (K ≃ₐ[E] K) → FiniteSIdele.localUnits E K v.1) 1 := fun _ => rfl

  let F : cocycles₂ (FiniteSIdele.localUnits E K v.1) :=
    mapCocycles₂ (MonoidHom.id _) ev (mapCocycles₂ (FiniteSIdele.D E K v.1).subtype (𝟙 _)
      (mapCocycles₂ (MonoidHom.id _) (GroupCohomology.RepPi.proj (SIdele.fibre E K S) (Sum.inl (Sum.inl v)))
        (mapCocycles₂ (MonoidHom.id _) (SIdele.diag E K S) f)))

  have hcoord : (groupCohomology.map (MonoidHom.id (K ≃ₐ[E] K))
        (GroupCohomology.RepPi.proj (NumberField.SIdele.fibre E K S) (Sum.inl (Sum.inl v))) 2 ≫
      (groupCohomology.coindIso (NumberField.FiniteSIdele.localUnits E K v.1) 2).hom).hom
      ((groupCohomology.map (MonoidHom.id (K ≃ₐ[E] K)) (NumberField.SIdele.diag E K S) 2).hom
        (H2π (SUnits.sUnitsRep E K S) f)) = H2π _ F := by
    rw [coindIso_hom_eq_map_subtype_comp_map_eval_one _ 2 ev hev]
    simp only [F, ModuleCat.hom_comp, LinearMap.comp_apply, H2π_comp_map_apply]
    rfl
  rw [hcoord]

  have hF : ∀ a b : FiniteSIdele.D E K v.1, F (a, b) =
      Additive.ofMul (Units.map (SUnits.loc E K v.1).toMonoidHom
        (SUnits.val E K S (f ((a : K ≃ₐ[E] K), (b : K ≃ₐ[E] K))))) := by
    intro a b
    change ((SUnits.diagIn E K S v).hom (f ((a : K ≃ₐ[E] K), (b : K ≃ₐ[E] K)))).1 1 = _
    rw [SUnits.diagIn_hom_apply_apply, one_smul]

  refine PlaceDecomp.H2π_eq_zero_of_exists_coboundary_above E K K'' w'' _ hw'' F y ?_
  intro g h a b ha hb
  rw [← hy g h, hF, ha, hb, toMul_ofMul]
  congr 1
  ext1
  simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, SUnits.loc]
  exact (HeightOneSpectrum.Extension.adicCompletionSemialgHom_coe K K'' _ _)
end

section

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Module CategoryTheory.Limits CategoryTheory.MonoidalCategory.Limits groupCohomology P2MW.S_groupCohomology_eq_zero_of_forall_continuousH2Map_primeLocal_eq_zero_pPrimary_continuousH2Sr_sUnitsMax.groupCohomology ExtCitation NumberField.LevelArith"
open scoped Classical NumberField.LevelArith TensorProduct Pointwise

namespace InvariantsPullback

variable {k G : Type} [CommRing k] [Group G] (A : Rep k G)
  (S₁ S₂ : Subgroup G) [S₁.Normal] [S₂.Normal] (hS : S₁ ≤ S₂)

private noncomputable def incl (w : A.quotientToInvariants S₂) : A.quotientToInvariants S₁ :=
  ⟨(w : A), fun s => w.2 ⟨(s : G), hS s.2⟩⟩

private theorem coe_incl (w : A.quotientToInvariants S₂) :
    ((incl A S₁ S₂ hS w : A.quotientToInvariants S₁) : A) = (w : A) :=
  rfl

private noncomputable def _root_.InvariantsPullback.proj : G ⧸ S₁ →* G ⧸ S₂ :=
  QuotientGroup.map S₁ S₂ (MonoidHom.id G) fun _ hx => hS hx

p2m_export "InvariantsPullback" "proj"
private theorem proj_mk (g : G) : proj S₁ S₂ hS (g : G ⧸ S₁) = (g : G ⧸ S₂) :=
  rfl

private noncomputable def pullback (f : cocycles₂ (A.quotientToInvariants S₂)) :
    cocycles₂ (A.quotientToInvariants S₁) :=
  ⟨fun x => incl A S₁ S₂ hS (f (proj S₁ S₂ hS x.1, proj S₁ S₂ hS x.2)), by
    rw [mem_cocycles₂_def]
    intro x y z
    induction x using QuotientGroup.induction_on with | H g => ?_
    induction y using QuotientGroup.induction_on with | H h => ?_
    induction z using QuotientGroup.induction_on with | H j => ?_
    have key :=
      (mem_cocycles₂_def f.1).1 f.2 (g : G ⧸ S₂) (h : G ⧸ S₂) (j : G ⧸ S₂)
    apply Subtype.ext
    have key' := congrArg (fun v : A.quotientToInvariants S₂ => (v : A)) key
    simp only [cocycles₂.val_eq_coe, Submodule.coe_sub, Submodule.coe_add, Submodule.coe_zero] at key'
    simp only [← QuotientGroup.mk_mul, proj_mk, Submodule.coe_sub, Submodule.coe_add, Submodule.coe_zero,
      coe_incl]
    (first | exact key' | simpa only [QuotientGroup.mk_mul] using key' | (have h__ := key'; simp only [QuotientGroup.mk_mul] at h__; exact h__))⟩

private theorem coe_pullback_mk (f : cocycles₂ (A.quotientToInvariants S₂)) (g h : G) :
    ((pullback A S₁ S₂ hS f ((g : G ⧸ S₁), (h : G ⧸ S₁)) : A.quotientToInvariants S₁) : A) =
      ((f ((g : G ⧸ S₂), (h : G ⧸ S₂)) : A.quotientToInvariants S₂) : A) :=
  rfl

end InvariantsPullback

namespace LevelRestriction

variable (S : Finset Nat.Primes) (L L' : IntermediateField ℚ (AlgebraicClosure ℚ))
  (hΓ : L'.fixingSubgroup ≤ L.fixingSubgroup)

private theorem ext_of_val {x y : sUnitsMaxRep S L} (h : sUnitsMaxRep.val S L x = sUnitsMaxRep.val S L y) :
    x = y :=
  Subtype.ext (Additive.toMul.injective h)

private theorem val_zero : sUnitsMaxRep.val S L (0 : sUnitsMaxRep S L) = 1 :=
  rfl

private noncomputable def carrierRes (x : sUnitsMaxRep S L) : sUnitsMaxRep S L' :=
  ⟨x.1, (mem_sUnitsMaxSubmodule S L' x.1).2 ((mem_sUnitsMaxStable_iff S L' _).2 fun γ =>
    (mem_sUnitsMaxStable_iff S L _).1 ((mem_sUnitsMaxSubmodule S L x.1).1 x.2)
      ⟨(γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), hΓ γ.2⟩)⟩

variable (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [Normal ℚ F]

private noncomputable def quotMap :
    ↥L'.fixingSubgroup ⧸ F.fixingSubgroup.comap L'.fixingSubgroup.subtype →*
      ↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype :=
  QuotientGroup.map _ _ (Subgroup.inclusion hΓ) fun _ hs => hs

private theorem quotMap_mk (g : ↥L'.fixingSubgroup) :
    quotMap L L' hΓ F (g : ↥L'.fixingSubgroup ⧸ F.fixingSubgroup.comap L'.fixingSubgroup.subtype) =
      ((Subgroup.inclusion hΓ g : ↥L.fixingSubgroup) :
        ↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype) :=
  rfl

private theorem qext
    {a b : (sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype)}
    (h : sUnitsMaxRep.val S L (a : sUnitsMaxRep S L) = sUnitsMaxRep.val S L (b : sUnitsMaxRep S L)) :
    a = b :=
  Subtype.ext (ext_of_val S L h)

private noncomputable def invRes
    (w : (sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype)) :
    (sUnitsMaxRep S L').quotientToInvariants (F.fixingSubgroup.comap L'.fixingSubgroup.subtype) :=
  ⟨carrierRes S L L' hΓ (w : sUnitsMaxRep S L), fun s => by
    apply ext_of_val
    have h := congrArg (sUnitsMaxRep.val S L)
      (w.2 (⟨Subgroup.inclusion hΓ (s : ↥L'.fixingSubgroup), s.2⟩ :
        ↥(F.fixingSubgroup.comap L.fixingSubgroup.subtype)))
    exact h⟩

private noncomputable def resLevel
    (f : cocycles₂ ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype))) :
    cocycles₂ ((sUnitsMaxRep S L').quotientToInvariants (F.fixingSubgroup.comap L'.fixingSubgroup.subtype)) :=
  ⟨fun x => invRes S L L' hΓ F (f (quotMap L L' hΓ F x.1, quotMap L L' hΓ F x.2)), by
    rw [mem_cocycles₂_def]
    intro x y z
    induction x using QuotientGroup.induction_on with | H g => ?_
    induction y using QuotientGroup.induction_on with | H h => ?_
    induction z using QuotientGroup.induction_on with | H j => ?_
    have key := (mem_cocycles₂_def f.1).1 f.2
      (Subgroup.inclusion hΓ g) (Subgroup.inclusion hΓ h) (Subgroup.inclusion hΓ j)
    apply qext
    have key' := congrArg
      (fun v : (sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype) =>
        sUnitsMaxRep.val S L (v : sUnitsMaxRep S L)) key
    simp only [cocycles₂.val_eq_coe, Submodule.coe_sub, Submodule.coe_add, Submodule.coe_zero,
      val_zero] at key'
    simp only [← QuotientGroup.mk_mul]
    simp only [quotMap_mk, map_mul, QuotientGroup.mk_mul, Submodule.coe_sub, Submodule.coe_add,
      Submodule.coe_zero, val_zero]
    exact key'⟩

private theorem val_resLevel
    (f : cocycles₂ ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype)))
    (g h : ↥L'.fixingSubgroup) :
    sUnitsMaxRep.val S L'
        (resLevel S L L' hΓ F f
          ((g : ↥L'.fixingSubgroup ⧸ F.fixingSubgroup.comap L'.fixingSubgroup.subtype),
            (h : ↥L'.fixingSubgroup ⧸ F.fixingSubgroup.comap L'.fixingSubgroup.subtype)) : sUnitsMaxRep S L') =
      sUnitsMaxRep.val S L
        (f (((Subgroup.inclusion hΓ g : ↥L.fixingSubgroup) :
              ↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype),
            ((Subgroup.inclusion hΓ h : ↥L.fixingSubgroup) :
              ↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype)) : sUnitsMaxRep S L) :=
  rfl

end LevelRestriction

namespace HasseSylowKill

private theorem H2π_map_res_eq_zero_of_forall_eq_sub_add
    {k G : Type} [CommRing k] [Group G] (A : Rep k G) (N : Subgroup G) [N.Normal] (K : Subgroup G)
    {Γ : Type} [Group Γ] (ι : Γ →* G) (hKι : ∀ g ∈ K, ∃ t : Γ, ι t = g)
    (f' : cocycles₂ (A.quotientToInvariants N)) (y : Γ → A)
    (hyinv : ∀ (t : Γ) (n : G), n ∈ N → A.ρ n (y t) = y t)
    (hyc : ∀ t s : Γ, ι s ∈ N → y (t * s) = y t)
    (hy : ∀ t u : Γ,
      ((f' ((ι t : G ⧸ N), (ι u : G ⧸ N)) : A.quotientToInvariants N) : A) = A.ρ (ι t) (y u) - y (t * u) + y t) :
    (map (K.map (QuotientGroup.mk' N)).subtype
        (𝟙 (Rep.res (K.map (QuotientGroup.mk' N)).subtype (A.quotientToInvariants N))) 2).hom
      (H2π _ f') = 0 := by

  have hsec : ∀ x : ↥(K.map (QuotientGroup.mk' N)), ∃ t : Γ, ((ι t : G) : G ⧸ N) = (x : G ⧸ N) := by
    intro x
    obtain ⟨g, hg, hgx⟩ := Subgroup.mem_map.mp x.2
    obtain ⟨t, rfl⟩ := hKι g hg
    refine ⟨t, ?_⟩
    rw [QuotientGroup.mk'_apply] at hgx
    exact hgx
  choose σ hσ using hsec

  have hyσ : ∀ x₁ x₂ : ↥(K.map (QuotientGroup.mk' N)), y (σ (x₁ * x₂)) = y (σ x₁ * σ x₂) := by
    intro x₁ x₂
    have h1 : ((ι (σ x₁ * σ x₂) : G) : G ⧸ N) = ((ι (σ (x₁ * x₂)) : G) : G ⧸ N) := by
      rw [map_mul, QuotientGroup.mk_mul, hσ x₁, hσ x₂, hσ (x₁ * x₂), Subgroup.coe_mul]
    have h2 : (ι (σ x₁ * σ x₂))⁻¹ * ι (σ (x₁ * x₂)) ∈ N := QuotientGroup.eq.mp h1
    rw [← map_inv, ← map_mul] at h2
    have h4 : σ (x₁ * x₂) = σ x₁ * σ x₂ * ((σ x₁ * σ x₂)⁻¹ * σ (x₁ * x₂)) := by
      rw [mul_inv_cancel_left]
    rw [h4, hyc (σ x₁ * σ x₂) _ h2]

  have hmem : ∀ x : ↥(K.map (QuotientGroup.mk' N)),
      y (σ x) ∈ Representation.invariants (A.ρ.comp N.subtype) := by
    intro x
    rw [Representation.mem_invariants]
    rintro ⟨n, hn⟩
    exact hyinv (σ x) n hn
  let c : ↥(K.map (QuotientGroup.mk' N)) → A.quotientToInvariants N := fun x => ⟨y (σ x), hmem x⟩
  rw [H2π_comp_map_apply, H2π_eq_zero_iff]
  refine ⟨c, ?_⟩
  funext x
  obtain ⟨x₁, x₂⟩ := x
  apply Subtype.ext
  have h := hy (σ x₁) (σ x₂)
  rw [hσ x₁, hσ x₂, ← hyσ x₁ x₂] at h
  have hρ₁ : (((Rep.res (K.map (QuotientGroup.mk' N)).subtype (A.quotientToInvariants N)).ρ x₁ (c x₂) :
      A.quotientToInvariants N) : A) = A.ρ (ι (σ x₁)) (y (σ x₂)) := by
    rw [Rep.coe_res_obj_ρ', Subgroup.coe_subtype, ← hσ x₁]
    rfl
  have hR : ((cochainsMap₂ (K.map (QuotientGroup.mk' N)).subtype
        (𝟙 (Rep.res (K.map (QuotientGroup.mk' N)).subtype (A.quotientToInvariants N))) f' (x₁, x₂) :
          A.quotientToInvariants N) : A) =
      ((f' ((x₁ : G ⧸ N), (x₂ : G ⧸ N)) : A.quotientToInvariants N) : A) := rfl
  rw [d₁₂_hom_apply, coe_mapCocycles₂]
  refine Eq.trans ?_ hR.symm
  refine Eq.trans
    (b := (((Rep.res (K.map (QuotientGroup.mk' N)).subtype (A.quotientToInvariants N)).ρ x₁ (c x₂) :
      A.quotientToInvariants N) : A) - y (σ (x₁ * x₂)) + y (σ x₁)) rfl ?_
  rw [hρ₁]
  exact h.symm

variable (S : Finset Nat.Primes) (L : IntermediateField ℚ (AlgebraicClosure ℚ))

private noncomputable def ofUnit (u : (AlgebraicClosure ℚ)ˣ) (hu : u ∈ sUnitsMax S) : sUnitsMaxRep S L :=
  ⟨Additive.ofMul u, by
    show Additive.toMul (Additive.ofMul u) ∈ sUnitsMaxStable S L
    rw [sUnitsMaxStable_eq_sUnitsMax]
    exact hu⟩

private theorem val_injective : Function.Injective (sUnitsMaxRep.val S L) :=
  fun _ _ h => Subtype.ext (Additive.toMul.injective h)

private theorem val_sub_add (a b c : sUnitsMaxRep S L) :
    sUnitsMaxRep.val S L (a - b + c) =
      sUnitsMaxRep.val S L a * (sUnitsMaxRep.val S L b)⁻¹ * sUnitsMaxRep.val S L c := rfl

private theorem map_res_H2π_eq_zero_of_le (L' F' : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLL' : L ≤ L')
    [Normal ℚ F']
    (f' : cocycles₂ ((sUnitsMaxRep S L).quotientToInvariants (F'.fixingSubgroup.comap L.fixingSubgroup.subtype)))
    (y : ↥L'.fixingSubgroup → (AlgebraicClosure ℚ)ˣ) (hyS : ∀ g, y g ∈ sUnitsMax S)
    (hyc : ∀ g s : ↥L'.fixingSubgroup,
      (s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ F'.fixingSubgroup → y (g * s) = y g)
    (hyinv : ∀ (g : ↥L'.fixingSubgroup) (s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
      s ∈ F'.fixingSubgroup → s • y g = y g)
    (hy : ∀ g h : ↥L'.fixingSubgroup,
      sUnitsMaxRep.val S L
          ((f' ((Subgroup.inclusion (IntermediateField.fixingSubgroup_le hLL') g :
                  ↥L.fixingSubgroup ⧸ F'.fixingSubgroup.comap L.fixingSubgroup.subtype),
                (Subgroup.inclusion (IntermediateField.fixingSubgroup_le hLL') h :
                  ↥L.fixingSubgroup ⧸ F'.fixingSubgroup.comap L.fixingSubgroup.subtype)) :
              (sUnitsMaxRep S L).quotientToInvariants _) : sUnitsMaxRep S L) =
        ((Subgroup.inclusion (IntermediateField.fixingSubgroup_le hLL') g : ↥L.fixingSubgroup) :
            AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) • y h * (y (g * h))⁻¹ * y g) :
    (map ((L'.fixingSubgroup.subgroupOf L.fixingSubgroup).map
            (QuotientGroup.mk' (F'.fixingSubgroup.comap L.fixingSubgroup.subtype))).subtype
        (𝟙 (Rep.res ((L'.fixingSubgroup.subgroupOf L.fixingSubgroup).map
            (QuotientGroup.mk' (F'.fixingSubgroup.comap L.fixingSubgroup.subtype))).subtype
          ((sUnitsMaxRep S L).quotientToInvariants (F'.fixingSubgroup.comap L.fixingSubgroup.subtype)))) 2).hom
      (H2π _ f') = 0 :=
  H2π_map_res_eq_zero_of_forall_eq_sub_add (sUnitsMaxRep S L) (F'.fixingSubgroup.comap L.fixingSubgroup.subtype)
    (L'.fixingSubgroup.subgroupOf L.fixingSubgroup) (Subgroup.inclusion (IntermediateField.fixingSubgroup_le hLL'))
    (fun g hg => ⟨⟨(g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), Subgroup.mem_subgroupOf.mp hg⟩, Subtype.ext rfl⟩)
    f' (fun g => ofUnit S L (y g) (hyS g))
    (fun g n hn => val_injective S L (hyinv g n hn))
    (fun g s hs => val_injective S L (hyc g s hs))
    (fun g h => val_injective S L ((hy g h).trans (val_sub_add S L
      ((sUnitsMaxRep S L).ρ (Subgroup.inclusion (IntermediateField.fixingSubgroup_le hLL') g)
        (ofUnit S L (y h) (hyS h)))
      (ofUnit S L (y (g * h)) (hyS (g * h))) (ofUnit S L (y g) (hyS g))).symm))

end HasseSylowKill

namespace HasseSylowKill

open InvariantsPullback LevelRestriction

private theorem exists_cocycle_coe_eq_and_map_res_H2π_eq_zero
    (S : Finset Nat.Primes) (L L' F F' : IntermediateField ℚ (AlgebraicClosure ℚ))
    (hLL' : L ≤ L') (hL'F : L' ≤ F) (hFF' : F ≤ F') [Normal ℚ F] [Normal ℚ F']
    (hΓ : L'.fixingSubgroup ≤ L.fixingSubgroup)
    (f : cocycles₂ ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype)))
    (y : ↥L'.fixingSubgroup → (AlgebraicClosure ℚ)ˣ) (hyS : ∀ g, y g ∈ sUnitsMax S)
    (hyc : ∀ g s : ↥L'.fixingSubgroup,
      (s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ F'.fixingSubgroup → y (g * s) = y g)
    (hyinv : ∀ (g : ↥L'.fixingSubgroup) (s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
      s ∈ F'.fixingSubgroup → s • y g = y g)
    (hy : ∀ g h : ↥L'.fixingSubgroup,
      sUnitsMaxRep.val S L
          ((f ((Subgroup.inclusion hΓ g :
                  ↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype),
                (Subgroup.inclusion hΓ h :
                  ↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype)) :
              (sUnitsMaxRep S L).quotientToInvariants _) : sUnitsMaxRep S L) =
        (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) • y h * (y (g * h))⁻¹ * y g) :
    ∃ f' : cocycles₂ ((sUnitsMaxRep S L).quotientToInvariants (F'.fixingSubgroup.comap L.fixingSubgroup.subtype)),
      (∀ g h : ↥L.fixingSubgroup,
        ((f' ((g : ↥L.fixingSubgroup ⧸ F'.fixingSubgroup.comap L.fixingSubgroup.subtype),
              (h : ↥L.fixingSubgroup ⧸ F'.fixingSubgroup.comap L.fixingSubgroup.subtype)) :
            (sUnitsMaxRep S L).quotientToInvariants _) : sUnitsMaxRep S L) =
          ((f ((g : ↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype),
              (h : ↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype)) :
            (sUnitsMaxRep S L).quotientToInvariants _) : sUnitsMaxRep S L)) ∧
      (map ((L'.fixingSubgroup.subgroupOf L.fixingSubgroup).map
              (QuotientGroup.mk' (F'.fixingSubgroup.comap L.fixingSubgroup.subtype))).subtype
          (𝟙 (Rep.res ((L'.fixingSubgroup.subgroupOf L.fixingSubgroup).map
              (QuotientGroup.mk' (F'.fixingSubgroup.comap L.fixingSubgroup.subtype))).subtype
            ((sUnitsMaxRep S L).quotientToInvariants (F'.fixingSubgroup.comap L.fixingSubgroup.subtype)))) 2).hom
        (H2π _ f') = 0 := by
  have _ := hL'F
  exact ⟨pullback (sUnitsMaxRep S L) _ _ (comap_fixingSubgroup_antitone L.fixingSubgroup.subtype hFF') f,
    fun g h =>
      coe_pullback_mk (sUnitsMaxRep S L) _ _ (comap_fixingSubgroup_antitone L.fixingSubgroup.subtype hFF') f g h,
    map_res_H2π_eq_zero_of_le S L L' F' hLL' _ y hyS hyc hyinv hy⟩

end HasseSylowKill
end

section

open NumberField.LevelArith

namespace CrepdPkg

private noncomputable def iotaOf {G H : Type} [Group G] [Group H] (f : G →* H)
    (hf : Function.Surjective f) (N : Subgroup G) [N.Normal] (hN : f.ker = N) : H →* G ⧸ N :=
  ((QuotientGroup.quotientKerEquivOfSurjective f hf).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hN)).toMonoidHom

private theorem iotaOf_bijective {G H : Type} [Group G] [Group H] (f : G →* H)
    (hf : Function.Surjective f) (N : Subgroup G) [N.Normal] (hN : f.ker = N) :
    Function.Bijective (iotaOf f hf N hN) :=
  ((QuotientGroup.quotientKerEquivOfSurjective f hf).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hN)).bijective

private theorem iotaOf_apply_f {G H : Type} [Group G] [Group H] (f : G →* H)
    (hf : Function.Surjective f) (N : Subgroup G) [N.Normal] (hN : f.ker = N) (g : G) :
    iotaOf f hf N hN (f g) = (g : G ⧸ N) := by
  have h : (QuotientGroup.quotientKerEquivOfSurjective f hf).symm (f g) = (g : G ⧸ f.ker) :=
    (MulEquiv.symm_apply_eq _).mpr (QuotientGroup.kerLift_mk f g).symm
  show QuotientGroup.quotientMulEquivOfEq hN
      ((QuotientGroup.quotientKerEquivOfSurjective f hf).symm (f g)) = (g : G ⧸ N)
  rw [h, QuotientGroup.quotientMulEquivOfEq_mk]

private theorem ker_eq_of_forall {G H : Type} [Group G] [Group H] (f : G →* H) (N : Subgroup G)
    (h : ∀ g : G, f g = 1 ↔ g ∈ N) : f.ker = N := by
  ext g
  rw [MonoidHom.mem_ker]
  exact h g

private theorem exists_res_hom_of_addEquiv {G H : Type} [Group G] [Group H] (ι : H →* G)
    (A : Rep ℤ G) (B : Rep ℤ H) (e : A ≃+ B)
    (he : ∀ (h : H) (x : A), e (A.ρ (ι h) x) = B.ρ h (e x)) :
    ∃ φ : Rep.res ι A ⟶ B, Function.Bijective φ.hom ∧ ∀ x, φ.hom x = e x := by
  letI := (Rep.res ι A).hV2
  letI := B.hV2
  exact ⟨Rep.homEquiv.symm
    { toFun := e, map_add' := e.map_add,
      map_smul' := fun n x => by simpa using map_intCast_smul e ℤ ℤ n x,
      isIntertwining' := fun h => LinearMap.ext fun x => he h x },
    e.bijective, fun _ => rfl⟩

private theorem levelGal_surjective (L F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLF : L ≤ F)
    [Normal ↥L ↥(levelField L F hLF)] : Function.Surjective (levelGal L F hLF) := by
  haveI : Normal ↥L (AlgebraicClosure ℚ) := Normal.tower_top_of_normal ℚ ↥L (AlgebraicClosure ℚ)
  unfold levelGal
  rw [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom]
  exact (AlgEquiv.restrictNormalHom_surjective (F := ↥L) (K₁ := ↥(levelField L F hLF))
    (AlgebraicClosure ℚ)).comp (IntermediateField.fixingSubgroupEquiv L).surjective

private theorem levelGal_ker (L F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLF : L ≤ F)
    [Normal ↥L ↥(levelField L F hLF)] :
    (levelGal L F hLF).ker = F.fixingSubgroup.comap L.fixingSubgroup.subtype := by
  refine ker_eq_of_forall _ _ fun γ => ⟨fun h1 => ?_, fun hγ => levelGal_eq_one_of_mem L F hLF γ hγ⟩
  rw [Subgroup.mem_comap, Subgroup.coe_subtype, IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  have hx' : ((levelGal L F hLF γ ⟨x, (IntermediateField.mem_extendScalars hLF).2 hx⟩ :
      ↥(levelField L F hLF)) : AlgebraicClosure ℚ) = x := by
    rw [h1]
    rfl
  rwa [levelGal_apply_coe] at hx'

private theorem exists_pkg (S : Finset Nat.Primes) (L F : IntermediateField ℚ (AlgebraicClosure ℚ))
    (hLF : L ≤ F) [FiniteDimensional ℚ ↥L] [FiniteDimensional ℚ ↥F] [Normal ℚ ↥F]
    [Normal ↥L ↥(levelField L F hLF)]
    (h9 : ∃ e : ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype))
        ≃+ (NumberField.SUnits.sUnitsRep ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S)),
      (∀ x, (((Additive.toMul ((e x).1) : (↥(levelField L F hLF))ˣ) : ↥(levelField L F hLF)) :
          AlgebraicClosure ℚ) =
        ((sUnitsMaxRep.val S L (x.1 : sUnitsMaxRep S L) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ)) ∧
      ∀ (g : ↥L.fixingSubgroup) (x),
        e (((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype)).ρ
            (g : ↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype) x) =
          (NumberField.SUnits.sUnitsRep ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S)).ρ
            (levelGal L F hLF g) (e x)) :
    ∃ (ι : (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) →*
          (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype))
      (_ : Function.Bijective ι)
      (_ : ∀ g : ↥L.fixingSubgroup,
        ι (levelGal L F hLF g) = (g : ↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype))
      (φ : Rep.res ι ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype)) ⟶
        NumberField.SUnits.sUnitsRep ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S))
      (_ : Function.Bijective φ.hom),
      ∀ x,
        ((NumberField.SUnits.val ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S) (φ.hom x) :
            ↥(levelField L F hLF)) : AlgebraicClosure ℚ)
          = ((sUnitsMaxRep.val S L (x.1 : sUnitsMaxRep S L) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) := by
  obtain ⟨e, he_val, he_ρ⟩ := h9
  have hsurj := levelGal_surjective L F hLF
  have hker := levelGal_ker L F hLF
  obtain ⟨φ, hφ, hφe⟩ := exists_res_hom_of_addEquiv (iotaOf (levelGal L F hLF) hsurj _ hker) _ _ e
    (fun σ x => by
      obtain ⟨g, rfl⟩ := hsurj σ
      rw [iotaOf_apply_f]
      exact he_ρ g x)
  refine ⟨iotaOf (levelGal L F hLF) hsurj _ hker, iotaOf_bijective _ hsurj _ hker,
    fun g => iotaOf_apply_f _ hsurj _ hker g, φ, hφ, fun x => ?_⟩
  rw [hφe x]
  exact he_val x

end CrepdPkg
end

section

p2m_open "IsDedekindDomain NumberField P2MW.S_groupCohomology_eq_zero_of_forall_continuousH2Map_primeLocal_eq_zero_pPrimary_continuousH2Sr_sUnitsMax.NumberField NumberField.LevelArith ExtCitation"

namespace HasseLevelFurniture

private theorem levelField_le (E F L : IntermediateField ℚ (AlgebraicClosure ℚ))
    (hEF : E ≤ F) (hEL : E ≤ L) (hFL : F ≤ L) :
    levelField E F hEF ≤ levelField E L hEL :=
  (IntermediateField.extendScalars_le_extendScalars_iff hEF hEL).2 hFL

private noncomputable abbrev levelAlgebra (E F L : IntermediateField ℚ (AlgebraicClosure ℚ))
    (hEF : E ≤ F) (hEL : E ≤ L) (hFL : F ≤ L) :
    Algebra ↥(levelField E F hEF) ↥(levelField E L hEL) :=
  (IntermediateField.inclusion (levelField_le E F L hEF hEL hFL)).toRingHom.toAlgebra

private theorem levelAlgebra_isScalarTower (E F L : IntermediateField ℚ (AlgebraicClosure ℚ))
    (hEF : E ≤ F) (hEL : E ≤ L) (hFL : F ≤ L) :
    letI := levelAlgebra E F L hEF hEL hFL
    IsScalarTower ↥E ↥(levelField E F hEF) ↥(levelField E L hEL) :=
  letI := levelAlgebra E F L hEF hEL hFL
  IsScalarTower.of_algebraMap_eq fun x =>
    ((IntermediateField.inclusion (levelField_le E F L hEF hEL hFL)).commutes x).symm

private theorem coe_levelAlgebraMap (E F L : IntermediateField ℚ (AlgebraicClosure ℚ))
    (hEF : E ≤ F) (hEL : E ≤ L) (hFL : F ≤ L) (x : ↥(levelField E F hEF)) :
    letI := levelAlgebra E F L hEF hEL hFL
    ((algebraMap ↥(levelField E F hEF) ↥(levelField E L hEL) x : ↥(levelField E L hEL)) : AlgebraicClosure ℚ) =
      (x : AlgebraicClosure ℚ) :=
  rfl

private theorem isGalois_levelField (E L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hEL : E ≤ L)
    [FiniteDimensional ℚ ↥L] [Normal ℚ ↥L] : IsGalois ↥E ↥(levelField E L hEL) := by
  haveI : IsGalois ℚ ↥L := ⟨⟩
  haveI : IsGalois ℚ ↥(levelField E L hEL) :=
    IsGalois.of_algEquiv
      (AlgEquiv.ofRingEquiv (f := levelFieldEquiv E L hEL) fun q =>
        (levelFieldEquiv E L hEL).toRingHom.map_rat_algebraMap q)
  haveI : IsScalarTower ℚ ↥E ↥(levelField E L hEL) := IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  exact IsGalois.tower_top_of_isGalois ℚ ↥E ↥(levelField E L hEL)

private theorem coe_restrictNormalHom_apply (E F L : IntermediateField ℚ (AlgebraicClosure ℚ))
    (hEF : E ≤ F) (hEL : E ≤ L) (hFL : F ≤ L) [Normal ↥E ↥(levelField E F hEF)]
    (σ : ↥(levelField E L hEL) ≃ₐ[↥E] ↥(levelField E L hEL)) (x : ↥(levelField E F hEF)) :
    letI := levelAlgebra E F L hEF hEL hFL
    haveI := levelAlgebra_isScalarTower E F L hEF hEL hFL
    ((AlgEquiv.restrictNormalHom ↥(levelField E F hEF) σ x : ↥(levelField E F hEF)) : AlgebraicClosure ℚ) =
      ((σ (algebraMap ↥(levelField E F hEF) ↥(levelField E L hEL) x) : ↥(levelField E L hEL)) :
        AlgebraicClosure ℚ) := by
  letI := levelAlgebra E F L hEF hEL hFL
  haveI := levelAlgebra_isScalarTower E F L hEF hEL hFL
  exact congrArg Subtype.val (AlgEquiv.restrictNormal_commutes σ ↥(levelField E F hEF) x)

private theorem mem_decomp_iff_restrictScalars_mem (E K : Type) [Field E] [Field K] [NumberField K] [Algebra E K]
    [Algebra ℚ E] [Algebra ℚ K] [IsScalarTower ℚ E K] (w : HeightOneSpectrum (𝓞 K)) (σ : K ≃ₐ[E] K) :
    σ ∈ PlaceDecomp.decomp E K w ↔ σ.restrictScalars ℚ ∈ PlaceDecomp.decomp ℚ K w :=
  Iff.rfl

private theorem restrictScalars_levelGal (E L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hEL : E ≤ L)
    [Normal ↥E ↥(levelField E L hEL)] [Algebra ℚ ↥(levelField E L hEL)]
    [@IsScalarTower ℚ ↥E ↥(levelField E L hEL)
      Algebra.toSMul Algebra.toSMul Algebra.toSMul]
    [@IsScalarTower ℚ ↥(levelField E L hEL) (AlgebraicClosure ℚ)
      Algebra.toSMul Algebra.toSMul Algebra.toSMul]
    [Normal ℚ ↥(levelField E L hEL)]
    (γ : ↥E.fixingSubgroup) :
    (levelGal E L hEL γ).restrictScalars ℚ =
      AlgEquiv.restrictNormalHom ↥(levelField E L hEL)
        (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) := by
  ext x
  exact (levelGal_apply_coe E L hEL γ x).trans
    (AlgEquiv.restrictNormal_commutes (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      ↥(levelField E L hEL) x).symm

private theorem normal_rat_levelField (E L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hEL : E ≤ L)
    [Algebra ℚ ↥(levelField E L hEL)] [Normal ℚ ↥L] : Normal ℚ ↥(levelField E L hEL) :=
  Normal.of_algEquiv
    (AlgEquiv.ofRingEquiv (f := levelFieldEquiv E L hEL) fun q =>
      (levelFieldEquiv E L hEL).toRingHom.map_rat_algebraMap q)

private theorem isScalarTower_rat_levelField_algClosure (E L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hEL : E ≤ L)
    [Algebra ℚ ↥(levelField E L hEL)] :
    @IsScalarTower ℚ ↥(levelField E L hEL) (AlgebraicClosure ℚ)
      Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)

private theorem isScalarTower_rat_base_levelField (E L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hEL : E ≤ L)
    [Algebra ℚ ↥(levelField E L hEL)] :
    @IsScalarTower ℚ ↥E ↥(levelField E L hEL) Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)

private theorem levelAlgebra_isScalarTower_algClosure (E F L : IntermediateField ℚ (AlgebraicClosure ℚ))
    (hEF : E ≤ F) (hEL : E ≤ L) (hFL : F ≤ L) :
    letI := levelAlgebra E F L hEF hEL hFL
    IsScalarTower ↥(levelField E F hEF) ↥(levelField E L hEL) (AlgebraicClosure ℚ) :=
  letI := levelAlgebra E F L hEF hEL hFL
  IsScalarTower.of_algebraMap_eq fun x => (coe_levelAlgebraMap E F L hEF hEL hFL x).symm

private theorem restrictNormalHom_levelGal (E F L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hEF : E ≤ F)
    (hEL : E ≤ L) (hFL : F ≤ L) [Normal ↥E ↥(levelField E F hEF)] [Normal ↥E ↥(levelField E L hEL)]
    (γ : ↥E.fixingSubgroup) :
    letI := levelAlgebra E F L hEF hEL hFL
    haveI := levelAlgebra_isScalarTower E F L hEF hEL hFL
    AlgEquiv.restrictNormalHom ↥(levelField E F hEF) (levelGal E L hEL γ) = levelGal E F hEF γ := by
  letI := levelAlgebra E F L hEF hEL hFL
  haveI := levelAlgebra_isScalarTower E F L hEF hEL hFL
  refine AlgEquiv.ext fun x => Subtype.ext ?_
  rw [coe_restrictNormalHom_apply E F L hEF hEL hFL (levelGal E L hEL γ) x, levelGal_apply_coe, levelGal_apply_coe]
  rfl

private noncomputable abbrev lamE (E : IntermediateField ℚ (AlgebraicClosure ℚ)) (q : Nat.Primes)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    ↥(E.fixingSubgroup.comap ((MulAut.conj σ).toMonoidHom.comp (primeLocalToGlobal q))) →* ↥E.fixingSubgroup :=
  ((MulAut.conj σ).toMonoidHom.comp (primeLocalToGlobal q)).subgroupComap E.fixingSubgroup

private noncomputable def resHom (E Kbig : IntermediateField ℚ (AlgebraicClosure ℚ)) (hEK : E ≤ Kbig)
    [FiniteDimensional ℚ ↥Kbig]
    [Normal ↥E ↥(levelField E Kbig hEK)] [Algebra ℚ ↥(levelField E Kbig hEK)]
    [@IsScalarTower ℚ ↥(levelField E Kbig hEK) (AlgebraicClosure ℚ)
      Algebra.toSMul Algebra.toSMul Algebra.toSMul]
    [Normal ℚ ↥(levelField E Kbig hEK)]
    (q : Nat.Primes) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (w : HeightOneSpectrum (𝓞 ↥(levelField E Kbig hEK)))
    (hrange : ((AlgEquiv.restrictNormalHom ↥(levelField E Kbig hEK)).comp
        ((MulAut.conj σ).toMonoidHom.comp (primeLocalToGlobal q))).range =
      PlaceDecomp.decomp ℚ ↥(levelField E Kbig hEK) w) :
    ↥(E.fixingSubgroup.comap ((MulAut.conj σ).toMonoidHom.comp (primeLocalToGlobal q))) →*
      ↥(PlaceDecomp.decomp ↥E ↥(levelField E Kbig hEK) w) :=
  ((levelGal E Kbig hEK).comp (lamE E q σ)).codRestrict (PlaceDecomp.decomp ↥E ↥(levelField E Kbig hEK) w)
    fun d => by
    haveI := isScalarTower_rat_base_levelField E Kbig hEK
    rw [mem_decomp_iff_restrictScalars_mem ↥E ↥(levelField E Kbig hEK) w, MonoidHom.comp_apply,
      restrictScalars_levelGal E Kbig hEK, ← hrange]
    exact MonoidHom.mem_range.2 ⟨(d : primeLocalGaloisGroup q), rfl⟩

private theorem coe_resHom (E Kbig : IntermediateField ℚ (AlgebraicClosure ℚ)) (hEK : E ≤ Kbig)
    [FiniteDimensional ℚ ↥Kbig]
    [Normal ↥E ↥(levelField E Kbig hEK)] [Algebra ℚ ↥(levelField E Kbig hEK)]
    [@IsScalarTower ℚ ↥(levelField E Kbig hEK) (AlgebraicClosure ℚ)
      Algebra.toSMul Algebra.toSMul Algebra.toSMul]
    [Normal ℚ ↥(levelField E Kbig hEK)]
    (q : Nat.Primes) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (w : HeightOneSpectrum (𝓞 ↥(levelField E Kbig hEK)))
    (hrange : ((AlgEquiv.restrictNormalHom ↥(levelField E Kbig hEK)).comp
        ((MulAut.conj σ).toMonoidHom.comp (primeLocalToGlobal q))).range =
      PlaceDecomp.decomp ℚ ↥(levelField E Kbig hEK) w)
    (d : ↥(E.fixingSubgroup.comap ((MulAut.conj σ).toMonoidHom.comp (primeLocalToGlobal q)))) :
    ((resHom E Kbig hEK q σ w hrange d : ↥(PlaceDecomp.decomp ↥E ↥(levelField E Kbig hEK) w)) :
        ↥(levelField E Kbig hEK) ≃ₐ[↥E] ↥(levelField E Kbig hEK)) =
      levelGal E Kbig hEK (lamE E q σ d) :=
  rfl

private theorem resHom_surjective (E Kbig : IntermediateField ℚ (AlgebraicClosure ℚ)) (hEK : E ≤ Kbig)
    [FiniteDimensional ℚ ↥Kbig]
    [Normal ↥E ↥(levelField E Kbig hEK)] [Algebra ℚ ↥(levelField E Kbig hEK)]
    [@IsScalarTower ℚ ↥(levelField E Kbig hEK) (AlgebraicClosure ℚ)
      Algebra.toSMul Algebra.toSMul Algebra.toSMul]
    [Normal ℚ ↥(levelField E Kbig hEK)]
    (q : Nat.Primes) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (w : HeightOneSpectrum (𝓞 ↥(levelField E Kbig hEK)))
    (hrange : ((AlgEquiv.restrictNormalHom ↥(levelField E Kbig hEK)).comp
        ((MulAut.conj σ).toMonoidHom.comp (primeLocalToGlobal q))).range =
      PlaceDecomp.decomp ℚ ↥(levelField E Kbig hEK) w)
    (hmap : (E.fixingSubgroup.comap ((MulAut.conj σ).toMonoidHom.comp (primeLocalToGlobal q))).map
          ((AlgEquiv.restrictNormalHom ↥(levelField E Kbig hEK)).comp
            ((MulAut.conj σ).toMonoidHom.comp (primeLocalToGlobal q))) =
        PlaceDecomp.decomp ℚ ↥(levelField E Kbig hEK) w ⊓
          (E.comap (IsScalarTower.toAlgHom ℚ ↥(levelField E Kbig hEK) (AlgebraicClosure ℚ))).fixingSubgroup) :
    Function.Surjective (resHom E Kbig hEK q σ w hrange) := by
  haveI := isScalarTower_rat_base_levelField E Kbig hEK
  rintro ⟨τ, hτ⟩
  have hτ' : τ.restrictScalars ℚ ∈
      (E.fixingSubgroup.comap ((MulAut.conj σ).toMonoidHom.comp (primeLocalToGlobal q))).map
        ((AlgEquiv.restrictNormalHom ↥(levelField E Kbig hEK)).comp
          ((MulAut.conj σ).toMonoidHom.comp (primeLocalToGlobal q))) := by
    rw [hmap]
    refine Subgroup.mem_inf.2 ⟨(mem_decomp_iff_restrictScalars_mem ↥E ↥(levelField E Kbig hEK) w τ).1 hτ, ?_⟩
    refine (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx => ?_
    have hxE : IsScalarTower.toAlgHom ℚ ↥(levelField E Kbig hEK) (AlgebraicClosure ℚ) x ∈ E := hx
    rw [IsScalarTower.toAlgHom_apply] at hxE
    have hxe : x = algebraMap ↥E ↥(levelField E Kbig hEK) ⟨_, hxE⟩ := Subtype.ext rfl
    show τ x = x
    rw [hxe]
    exact τ.commutes _
  obtain ⟨d, hd, hdτ⟩ := Subgroup.mem_map.1 hτ'
  refine ⟨⟨d, hd⟩, Subtype.ext ?_⟩
  rw [coe_resHom]
  refine AlgEquiv.restrictScalars_injective (R := ℚ) ?_
  rw [restrictScalars_levelGal E Kbig hEK]
  exact hdτ

private theorem mem_fixingSubgroup_of_resHom_eq_one (E Kbig : IntermediateField ℚ (AlgebraicClosure ℚ))
    (hEK : E ≤ Kbig) [FiniteDimensional ℚ ↥Kbig]
    [Normal ↥E ↥(levelField E Kbig hEK)] [Algebra ℚ ↥(levelField E Kbig hEK)]
    [@IsScalarTower ℚ ↥(levelField E Kbig hEK) (AlgebraicClosure ℚ)
      Algebra.toSMul Algebra.toSMul Algebra.toSMul]
    [Normal ℚ ↥(levelField E Kbig hEK)]
    (q : Nat.Primes) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (w : HeightOneSpectrum (𝓞 ↥(levelField E Kbig hEK)))
    (hrange : ((AlgEquiv.restrictNormalHom ↥(levelField E Kbig hEK)).comp
        ((MulAut.conj σ).toMonoidHom.comp (primeLocalToGlobal q))).range =
      PlaceDecomp.decomp ℚ ↥(levelField E Kbig hEK) w)
    (d : ↥(E.fixingSubgroup.comap ((MulAut.conj σ).toMonoidHom.comp (primeLocalToGlobal q))))
    (hd : resHom E Kbig hEK q σ w hrange d = 1) :
    ((MulAut.conj σ).toMonoidHom.comp (primeLocalToGlobal q)) (d : primeLocalGaloisGroup q) ∈
      Kbig.fixingSubgroup := by
  have h0 := congrArg Subtype.val hd
  have h1 : levelGal E Kbig hEK (lamE E q σ d) = 1 := h0
  refine (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun y hy => ?_
  have h2 := levelGal_apply_coe E Kbig hEK (lamE E q σ d) ⟨y, (IntermediateField.mem_extendScalars hEK).2 hy⟩
  rw [h1, AlgEquiv.one_apply] at h2
  exact h2.symm

end HasseLevelFurniture
end

section

p2m_open "NumberField P2MW.S_groupCohomology_eq_zero_of_forall_continuousH2Map_primeLocal_eq_zero_pPrimary_continuousH2Sr_sUnitsMax.NumberField IsDedekindDomain"
open scoped Pointwise

open MulAction

namespace DecompositionAssembly

variable {Γ : Type*} [Group Γ]

private theorem map_topologicalClosure_le [TopologicalSpace Γ] [IsTopologicalGroup Γ] {Δ : Type*} [Group Δ]
    (r : Γ →* Δ) (U : Subgroup Γ) (hU : IsOpen (U : Set Γ)) (hUr : U ≤ r.ker) (R : Subgroup Γ) :
    R.topologicalClosure.map r ≤ R.map r := by
  rintro _ ⟨g, hg, rfl⟩
  have hg' : g ∈ closure (R : Set Γ) := hg
  have hopen : IsOpen ((fun x : Γ => g⁻¹ * x) ⁻¹' (U : Set Γ)) := hU.preimage (continuous_const_mul g⁻¹)
  have hmem : g ∈ (fun x : Γ => g⁻¹ * x) ⁻¹' (U : Set Γ) := by
    simp [U.one_mem]
  obtain ⟨x, hxU, hxR⟩ := mem_closure_iff.1 hg' _ hopen hmem
  refine ⟨x, hxR, ?_⟩
  have hker : r (g⁻¹ * x) = 1 := MonoidHom.mem_ker.1 (hUr hxU)
  calc r x = r g * r (g⁻¹ * x) := by rw [map_mul, map_inv, mul_inv_cancel_left]
    _ = r g := by rw [hker, mul_one]

private theorem comp_conj {Δ : Type*} [Group Δ] (r : Γ →* Δ) (σ : Γ) :
    r.comp (MulAut.conj σ).toMonoidHom = (MulAut.conj (r σ)).toMonoidHom.comp r := by
  ext x
  simp

private theorem range_comp_conj_comp_eq [TopologicalSpace Γ] [IsTopologicalGroup Γ] {Δ G α : Type*} [Group Δ]
    [Group G] [MulAction Γ α] (r : Γ →* Δ) (U : Subgroup Γ) (hU : IsOpen (U : Set Γ)) (hUr : U ≤ r.ker) (ℓ : G →* Γ)
    (A : α)
    (hℓ : ℓ.range ≤ stabilizer Γ A) (hdense : stabilizer Γ A ≤ ℓ.range.topologicalClosure) (σ : Γ)
    (D : Subgroup Δ) (hD : (stabilizer Γ (σ • A)).map r = D) :
    (r.comp ((MulAut.conj σ).toMonoidHom.comp ℓ)).range = D := by
  subst hD
  rw [stabilizer_smul_eq_stabilizer_map_conj, Subgroup.map_map, comp_conj, ← Subgroup.map_map,
    MonoidHom.range_comp, MonoidHom.range_comp, Subgroup.map_map, comp_conj, ← Subgroup.map_map]
  apply le_antisymm
  · exact Subgroup.map_mono (Subgroup.map_mono hℓ)
  · exact Subgroup.map_mono ((Subgroup.map_mono hdense).trans (map_topologicalClosure_le r U hU hUr _))

private theorem map_comap_eq_inf {Δ G : Type*} [Group Δ] [Group G] (r : Γ →* Δ) (g : G →* Γ) (D : Subgroup Δ)
    (hmain : (r.comp g).range = D) (Φ : Subgroup Γ) (Φ' : Subgroup Δ) (hΦ : ∀ γ, γ ∈ Φ ↔ r γ ∈ Φ') :
    (Φ.comap g).map (r.comp g) = D ⊓ Φ' := by
  ext δ
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    refine ⟨?_, (hΦ (g τ)).1 (Subgroup.mem_comap.1 hτ)⟩
    rw [← hmain]
    exact ⟨τ, rfl⟩
  · rintro ⟨hδD, hδΦ'⟩
    have hδ : δ ∈ (r.comp g).range := by rw [hmain]; exact hδD
    obtain ⟨τ, rfl⟩ := MonoidHom.mem_range.1 hδ
    exact ⟨τ, Subgroup.mem_comap.2 ((hΦ (g τ)).2 hδΦ'), rfl⟩

end DecompositionAssembly

namespace PlaceConjugate

private theorem mem_asIdeal_iff_of_ne_zero {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    {y : 𝓞 K} (hy : y ≠ 0) :
    y ∈ v.asIdeal ↔ v.valuation K (y : K) ≤ 1 ∧ ¬ v.valuation K ((y : K)⁻¹) ≤ 1 := by
  have hlt : v.valuation K (y : K) < 1 ↔ y ∈ v.asIdeal := v.valuation_lt_one_iff_mem y
  have h0 : 0 < v.valuation K (y : K) := by
    rw [zero_lt_iff, ne_eq, map_eq_zero]
    exact_mod_cast hy
  rw [← hlt, map_inv₀]
  constructor
  · intro h
    exact ⟨h.le, not_le.2 ((one_lt_inv₀ h0).2 h)⟩
  · rintro ⟨-, h2⟩
    exact (one_lt_inv₀ h0).1 (not_le.1 h2)

private theorem liesOver_span_of_mem {K : Type*} [Field K] [NumberField K] (P : Ideal (𝓞 K)) [P.IsPrime] {q : ℕ}
    (hq : q.Prime) (hqP : (q : 𝓞 K) ∈ P) : P.LiesOver (Ideal.span {(q : ℤ)}) := by
  have hmax : (Ideal.span {(q : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.1 hq).irreducible
  have hle : Ideal.span {(q : ℤ)} ≤ P.under ℤ := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    change algebraMap ℤ (𝓞 K) (q : ℤ) ∈ P
    rw [map_natCast]
    exact hqP
  have hne : P.under ℤ ≠ ⊤ := Ideal.IsPrime.ne_top inferInstance
  have heq : Ideal.span {(q : ℤ)} = P.under ℤ := hmax.eq_of_le hne hle
  exact ⟨heq⟩

private theorem exists_smul_eq_of_liesOver (N : Type*) [Field N] [NumberField N] [IsGalois ℚ N]
    (p : Ideal ℤ) (P Q : Ideal (𝓞 N)) [P.IsPrime] [P.LiesOver p] [Q.IsPrime] [Q.LiesOver p] :
    ∃ σ : N ≃ₐ[ℚ] N, σ • P = Q :=
  Ideal.exists_smul_eq_of_isGaloisGroup p P Q (N ≃ₐ[ℚ] N)

private theorem under_eq_of_forall_mem_iff (A : ValuationSubring (AlgebraicClosure ℚ)) (K₁ K₂ : Type*) [Field K₁]
    [Field K₂] [NumberField K₁] [NumberField K₂] [Algebra K₁ (AlgebraicClosure ℚ)] [Algebra K₂ (AlgebraicClosure ℚ)]
    [Algebra K₁ K₂] [IsScalarTower K₁ K₂ (AlgebraicClosure ℚ)] (w₁ : HeightOneSpectrum (𝓞 K₁))
    (h₁ : ∀ x : K₁, algebraMap K₁ (AlgebraicClosure ℚ) x ∈ A ↔ w₁.valuation K₁ x ≤ 1)
    (w₂ : HeightOneSpectrum (𝓞 K₂))
    (h₂ : ∀ x : K₂, algebraMap K₂ (AlgebraicClosure ℚ) x ∈ A ↔ w₂.valuation K₂ x ≤ 1) :
    HeightOneSpectrum.under (𝓞 K₁) w₂ = w₁ := by
  apply HeightOneSpectrum.ext
  ext y
  change algebraMap (𝓞 K₁) (𝓞 K₂) y ∈ w₂.asIdeal ↔ y ∈ w₁.asIdeal
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  have hy₂ : algebraMap (𝓞 K₁) (𝓞 K₂) y ≠ 0 := by
    intro h0
    apply hy
    have h1 : algebraMap K₁ K₂ (y : K₁) = 0 := by
      change ((algebraMap (𝓞 K₁) (𝓞 K₂) y : 𝓞 K₂) : K₂) = 0
      rw [h0]
      rfl
    have hzero : (y : K₁) = 0 := (algebraMap K₁ K₂).injective (h1.trans (map_zero _).symm)
    exact RingOfIntegers.coe_eq_zero_iff.1 hzero
  have hcoe : algebraMap K₂ (AlgebraicClosure ℚ) ((algebraMap (𝓞 K₁) (𝓞 K₂) y : 𝓞 K₂) : K₂) =
      algebraMap K₁ (AlgebraicClosure ℚ) (y : K₁) := by
    change algebraMap K₂ (AlgebraicClosure ℚ) (algebraMap K₁ K₂ (y : K₁)) = _
    rw [← IsScalarTower.algebraMap_apply]
  rw [mem_asIdeal_iff_of_ne_zero w₂ hy₂, mem_asIdeal_iff_of_ne_zero w₁ hy, ← h₂, ← h₂, ← h₁, ← h₁, map_inv₀,
    map_inv₀, hcoe]

variable (q : ℕ) [Fact q.Prime]

private theorem inv_natCast_notMem_padicPlace : ((q : AlgebraicClosure ℚ))⁻¹ ∉ padicPlace q := by
  rw [mem_padicPlace_iff, map_inv₀, map_natCast, nnnorm_inv, ← PadicAlgCl.valuation_def,
    PadicAlgCl.valuation_p, one_div, inv_inv, not_le]
  exact_mod_cast (Fact.out : q.Prime).one_lt

private theorem algebraMap_inv_natCast_notMem_smul_padicPlace (L : Type*) [Field L] [Algebra L (AlgebraicClosure ℚ)]
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    algebraMap L (AlgebraicClosure ℚ) (q : L)⁻¹ ∉ σ • padicPlace q := by
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, map_inv₀, map_natCast, map_inv₀,
    map_natCast]
  exact inv_natCast_notMem_padicPlace q

private theorem exists_forall_mem_iff_of_fixed (L : Type) [Field L] [NumberField L] [Algebra L (AlgebraicClosure ℚ)]
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    ∃ v : HeightOneSpectrum (𝓞 L),
      ∀ x : L, algebraMap L (AlgebraicClosure ℚ) x ∈ σ • padicPlace q ↔ v.valuation L x ≤ 1 := by
  obtain ⟨v, hv, -⟩ := NumberField.existsUnique_heightOneSpectrum_forall_map_mem_iff_valuation_le_one L
    (algebraMap L (AlgebraicClosure ℚ)) (σ • padicPlace q) ⟨_, algebraMap_inv_natCast_notMem_smul_padicPlace q L σ⟩
  exact ⟨v, hv⟩

private theorem exists_forall_mem_iff (K : Type) [Field K] [NumberField K] [Algebra K (AlgebraicClosure ℚ)]
    [IsScalarTower ℚ K (AlgebraicClosure ℚ)] [IsGalois ℚ K] (w : HeightOneSpectrum (𝓞 K))
    (hw : (q : 𝓞 K) ∈ w.asIdeal) :
    ∃ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      ∀ x : K, algebraMap K (AlgebraicClosure ℚ) x ∈ σ • padicPlace q ↔ w.valuation K x ≤ 1 := by
  have hq : q.Prime := Fact.out

  obtain ⟨v, hv⟩ := exists_forall_mem_iff_of_fixed q K 1
  simp only [one_smul] at hv
  have hqinv : algebraMap K (AlgebraicClosure ℚ) (q : K)⁻¹ ∉ padicPlace q := by
    have h := algebraMap_inv_natCast_notMem_smul_padicPlace q K 1
    rwa [one_smul] at h
  have hqv : (q : 𝓞 K) ∈ v.asIdeal := by
    have hq0 : (q : 𝓞 K) ≠ 0 := by exact_mod_cast hq.ne_zero
    have hle : v.valuation K ((q : 𝓞 K) : K) ≤ 1 := v.valuation_le_one (q : 𝓞 K)
    have hcast : ((q : 𝓞 K) : K) = (q : K) := map_natCast (algebraMap (𝓞 K) K) q
    refine (mem_asIdeal_iff_of_ne_zero v hq0).2 ⟨hle, fun h => hqinv ?_⟩
    rw [hcast] at h
    exact (hv _).2 h

  haveI := liesOver_span_of_mem v.asIdeal hq hqv
  haveI := liesOver_span_of_mem w.asIdeal hq hw
  obtain ⟨τ, hτ⟩ := exists_smul_eq_of_liesOver K (Ideal.span {(q : ℤ)}) v.asIdeal w.asIdeal
  obtain ⟨σ, hσ⟩ := AlgEquiv.restrictNormalHom_surjective (F := ℚ) (K₁ := K) (E := AlgebraicClosure ℚ) τ
  refine ⟨σ, ?_⟩
  have hres : AlgEquiv.restrictNormal σ⁻¹ K = τ⁻¹ := by
    rw [← hσ, ← map_inv]
    rfl
  have hσinv : ∀ x : K, σ⁻¹ (algebraMap K (AlgebraicClosure ℚ) x) = algebraMap K (AlgebraicClosure ℚ) (τ⁻¹ x) := by
    intro x
    rw [← hres]
    exact (AlgEquiv.restrictNormal_commutes σ⁻¹ K x).symm
  have hmem : ∀ x : K, algebraMap K (AlgebraicClosure ℚ) x ∈ σ • padicPlace q ↔ v.valuation K (τ⁻¹ x) ≤ 1 := by
    intro x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, hσinv, hv]

  obtain ⟨u, hu⟩ := exists_forall_mem_iff_of_fixed q K σ
  suffices huw : u = w by
    intro x
    rw [hu, huw]
  apply HeightOneSpectrum.ext
  ext y
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  have hy' : τ⁻¹ • y ≠ 0 := fun h => hy ((smul_eq_zero_iff_eq τ⁻¹).1 h)
  rw [← hτ, Ideal.mem_pointwise_smul_iff_inv_smul_mem, mem_asIdeal_iff_of_ne_zero u hy,
    mem_asIdeal_iff_of_ne_zero v hy', ← hu, ← hu, hmem, hmem]
  simp only [map_inv₀]
  rfl

end PlaceConjugate

namespace PlaceConjugate

open DecompositionAssembly

section Transport

variable (F Ω : Type*) [Field F] [Field Ω] [Algebra F Ω] (K : Type*) [Field K] [Algebra F K] [Algebra K Ω]
  [IsScalarTower F K Ω]

private noncomputable def toImage : K ≃ₐ[F] (IsScalarTower.toAlgHom F K Ω).fieldRange :=
  AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F K Ω)

private theorem coe_toImage (x : K) : (toImage F Ω K x : Ω) = algebraMap K Ω x :=
  rfl

private noncomputable def autEquiv :
    ((IsScalarTower.toAlgHom F K Ω).fieldRange ≃ₐ[F] (IsScalarTower.toAlgHom F K Ω).fieldRange) ≃* (K ≃ₐ[F] K) :=
  AlgEquiv.autCongr (toImage F Ω K).symm

private theorem autEquiv_apply
    (ψ : (IsScalarTower.toAlgHom F K Ω).fieldRange ≃ₐ[F] (IsScalarTower.toAlgHom F K Ω).fieldRange) (x : K) :
    autEquiv F Ω K ψ x = (toImage F Ω K).symm (ψ (toImage F Ω K x)) :=
  rfl

private theorem map_decompositionSubgroup_autEquiv (B : ValuationSubring Ω) :
    ((B.comap (algebraMap (IsScalarTower.toAlgHom F K Ω).fieldRange Ω)).decompositionSubgroup F).map
        (autEquiv F Ω K).toMonoidHom =
      (B.comap (algebraMap K Ω)).decompositionSubgroup F := by
  have key0 : ∀ x : K, toImage F Ω K x ∈ B.comap (algebraMap (IsScalarTower.toAlgHom F K Ω).fieldRange Ω) ↔
      x ∈ B.comap (algebraMap K Ω) := by
    intro x
    rw [ValuationSubring.mem_comap, ValuationSubring.mem_comap, IntermediateField.algebraMap_apply, coe_toImage]
  ext δ
  obtain ⟨ψ, rfl⟩ := (autEquiv F Ω K).surjective δ
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply, MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]
  have key : ∀ x : K, x ∈ autEquiv F Ω K ψ • B.comap (algebraMap K Ω) ↔
      toImage F Ω K x ∈ ψ • B.comap (algebraMap (IsScalarTower.toAlgHom F K Ω).fieldRange Ω) := by
    intro x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
      AlgEquiv.smul_def, AlgEquiv.smul_def, ← map_inv, autEquiv_apply, ValuationSubring.mem_comap,
      ValuationSubring.mem_comap, IntermediateField.algebraMap_apply, ← coe_toImage F Ω K, AlgEquiv.apply_symm_apply]
  constructor
  · intro h
    refine ValuationSubring.ext _ _ fun x => ?_
    rw [key, h, key0]
  · intro h
    refine ValuationSubring.ext _ _ fun z => ?_
    obtain ⟨x, rfl⟩ := (toImage F Ω K).surjective z
    rw [← key, h, key0]

variable [Normal F K]

private scoped instance : Normal F (IsScalarTower.toAlgHom F K Ω).fieldRange :=
  Normal.of_algEquiv (toImage F Ω K)

private theorem restrictNormalHom_eq :
    (AlgEquiv.restrictNormalHom K : (Ω ≃ₐ[F] Ω) →* (K ≃ₐ[F] K)) =
      (autEquiv F Ω K).toMonoidHom.comp (AlgEquiv.restrictNormalHom (IsScalarTower.toAlgHom F K Ω).fieldRange) := by
  ext γ x
  change AlgEquiv.restrictNormalHom K γ x =
    autEquiv F Ω K (AlgEquiv.restrictNormalHom (IsScalarTower.toAlgHom F K Ω).fieldRange γ) x
  rw [autEquiv_apply]
  apply (toImage F Ω K).injective
  rw [AlgEquiv.apply_symm_apply]
  apply Subtype.ext
  have h1 : algebraMap K Ω (AlgEquiv.restrictNormalHom K γ x) = γ (algebraMap K Ω x) :=
    AlgEquiv.restrictNormal_commutes γ K x
  have h2 : ((AlgEquiv.restrictNormalHom (IsScalarTower.toAlgHom F K Ω).fieldRange γ (toImage F Ω K x) :
      (IsScalarTower.toAlgHom F K Ω).fieldRange) : Ω) = γ (toImage F Ω K x : Ω) :=
    AlgEquiv.restrictNormal_commutes γ (IsScalarTower.toAlgHom F K Ω).fieldRange (toImage F Ω K x)
  rw [coe_toImage, h1, h2, coe_toImage]

private theorem map_restrictNormalHom_decompositionSubgroup_eq_of_forall
    (h : ∀ (L : IntermediateField F Ω) [Normal F L] (A : ValuationSubring Ω),
      (A.decompositionSubgroup F).map (AlgEquiv.restrictNormalHom L) =
        (A.comap (algebraMap L Ω)).decompositionSubgroup F)
    (A : ValuationSubring Ω) :
    (A.decompositionSubgroup F).map (AlgEquiv.restrictNormalHom K) =
      (A.comap (algebraMap K Ω)).decompositionSubgroup F := by
  rw [restrictNormalHom_eq F Ω K, ← Subgroup.map_map, h _ A, map_decompositionSubgroup_autEquiv F Ω K]

private theorem fixingSubgroup_le_ker :
    (IsScalarTower.toAlgHom F K Ω).fieldRange.fixingSubgroup ≤
      (AlgEquiv.restrictNormalHom K : (Ω ≃ₐ[F] Ω) →* (K ≃ₐ[F] K)).ker := by
  intro γ hγ
  rw [IntermediateField.mem_fixingSubgroup_iff] at hγ
  rw [MonoidHom.mem_ker]
  refine AlgEquiv.ext fun x => (algebraMap K Ω).injective ?_
  have h1 : algebraMap K Ω (AlgEquiv.restrictNormalHom K γ x) = γ (algebraMap K Ω x) :=
    AlgEquiv.restrictNormal_commutes γ K x
  rw [h1, AlgEquiv.one_apply]
  exact hγ _ ⟨x, rfl⟩

private theorem mem_fixingSubgroup_iff_restrictNormalHom_mem {E : IntermediateField F Ω}
    (hE : E ≤ (IsScalarTower.toAlgHom F K Ω).fieldRange) (γ : Ω ≃ₐ[F] Ω) :
    γ ∈ E.fixingSubgroup ↔
      AlgEquiv.restrictNormalHom K γ ∈ (E.comap (IsScalarTower.toAlgHom F K Ω)).fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff, IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h y hy
    have h1 : algebraMap K Ω (AlgEquiv.restrictNormalHom K γ y) = γ (algebraMap K Ω y) :=
      AlgEquiv.restrictNormal_commutes γ K y
    apply (algebraMap K Ω).injective
    rw [h1]
    exact h _ hy
  · intro h x hx
    obtain ⟨y, rfl⟩ := hE hx
    have h1 : algebraMap K Ω (AlgEquiv.restrictNormalHom K γ y) = γ (algebraMap K Ω y) :=
      AlgEquiv.restrictNormal_commutes γ K y
    have h2 : AlgEquiv.restrictNormalHom K γ y = y := h y hx
    change γ (algebraMap K Ω y) = algebraMap K Ω y
    rw [← h1, h2]

end Transport

variable (q : ℕ) [Fact q.Prime] (K : Type) [Field K] [NumberField K] [Algebra K (AlgebraicClosure ℚ)]
  [IsScalarTower ℚ K (AlgebraicClosure ℚ)] [Normal ℚ K] (w : HeightOneSpectrum (𝓞 K))

private theorem range_eq_decomp_of_forall_mem_iff (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (hσ : ∀ x : K, algebraMap K (AlgebraicClosure ℚ) x ∈ σ • padicPlace q ↔ w.valuation K x ≤ 1) :
    ((AlgEquiv.restrictNormalHom K).comp ((MulAut.conj σ).toMonoidHom.comp (localGaloisToGlobal q))).range =
      PlaceDecomp.decomp ℚ K w := by
  have hW : (σ • padicPlace q).comap (algebraMap K (AlgebraicClosure ℚ)) = (w.valuation K).valuationSubring :=
    ValuationSubring.ext _ _ fun x => by
      rw [ValuationSubring.mem_comap, Valuation.mem_valuationSubring_iff]
      exact hσ x
  have hD : ((σ • padicPlace q).decompositionSubgroup ℚ).map (AlgEquiv.restrictNormalHom K) =
      PlaceDecomp.decomp ℚ K w := by
    have h := map_restrictNormalHom_decompositionSubgroup_eq_of_forall ℚ (AlgebraicClosure ℚ) K
      (fun L _ A => ValuationSubring.map_restrictNormalHom_decompositionSubgroup_eq L A) (σ • padicPlace q)
    rw [hW] at h
    exact h
  haveI : FiniteDimensional ℚ (IsScalarTower.toAlgHom ℚ K (AlgebraicClosure ℚ)).fieldRange :=
    (IsScalarTower.toAlgHom ℚ K (AlgebraicClosure ℚ)).toLinearMap.finiteDimensional_range
  refine range_comp_conj_comp_eq (AlgEquiv.restrictNormalHom K) _
    (IsScalarTower.toAlgHom ℚ K (AlgebraicClosure ℚ)).fieldRange.fixingSubgroup_isOpen
    (fixingSubgroup_le_ker ℚ (AlgebraicClosure ℚ) K)
    (localGaloisToGlobal q) (padicPlace q) ?_
    (ValuationSubring.decompositionSubgroup_padicPlace_le_closure_range_localGaloisToGlobal q) σ _ hD
  rintro _ ⟨t, rfl⟩
  exact localGaloisToGlobal_mem_decompositionSubgroup q t

private theorem map_comap_fixingSubgroup_eq_of_forall_mem_iff (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (hσ : ∀ x : K, algebraMap K (AlgebraicClosure ℚ) x ∈ σ • padicPlace q ↔ w.valuation K x ≤ 1)
    (E : IntermediateField ℚ (AlgebraicClosure ℚ))
    (hE : E ≤ (IsScalarTower.toAlgHom ℚ K (AlgebraicClosure ℚ)).fieldRange) :
    (E.fixingSubgroup.comap ((MulAut.conj σ).toMonoidHom.comp (localGaloisToGlobal q))).map
        ((AlgEquiv.restrictNormalHom K).comp ((MulAut.conj σ).toMonoidHom.comp (localGaloisToGlobal q))) =
      PlaceDecomp.decomp ℚ K w ⊓ (E.comap (IsScalarTower.toAlgHom ℚ K (AlgebraicClosure ℚ))).fixingSubgroup :=
  map_comap_eq_inf (AlgEquiv.restrictNormalHom K) _ _ (range_eq_decomp_of_forall_mem_iff q K w σ hσ)
    E.fixingSubgroup _ (mem_fixingSubgroup_iff_restrictNormalHom_mem ℚ (AlgebraicClosure ℚ) K hE)

end PlaceConjugate
p2m_reactivate "P2MW.S_groupCohomology_eq_zero_of_forall_continuousH2Map_primeLocal_eq_zero_pPrimary_continuousH2Sr_sUnitsMax.PlaceConjugate"

namespace PlaceConjugate

open ExtCitation

variable (q : Nat.Primes) [Fact (q : ℕ).Prime] (K : Type) [Field K] [NumberField K] [Algebra K (AlgebraicClosure ℚ)]
  [IsScalarTower ℚ K (AlgebraicClosure ℚ)] (w : HeightOneSpectrum (𝓞 K))

private theorem range_eq_decomp_of_forall_mem_iff' [Normal ℚ K] (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (hσ : ∀ x : K, algebraMap K (AlgebraicClosure ℚ) x ∈ σ • padicPlace q ↔ w.valuation K x ≤ 1) :
    ((AlgEquiv.restrictNormalHom K).comp ((MulAut.conj σ).toMonoidHom.comp (primeLocalToGlobal q))).range =
      PlaceDecomp.decomp ℚ K w :=
  range_eq_decomp_of_forall_mem_iff (q : ℕ) K w σ hσ

private theorem map_comap_fixingSubgroup_eq_of_forall_mem_iff' [Normal ℚ K]
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (hσ : ∀ x : K, algebraMap K (AlgebraicClosure ℚ) x ∈ σ • padicPlace q ↔ w.valuation K x ≤ 1)
    (E : IntermediateField ℚ (AlgebraicClosure ℚ))
    (hE : E ≤ (IsScalarTower.toAlgHom ℚ K (AlgebraicClosure ℚ)).fieldRange) :
    (E.fixingSubgroup.comap ((MulAut.conj σ).toMonoidHom.comp (primeLocalToGlobal q))).map
        ((AlgEquiv.restrictNormalHom K).comp ((MulAut.conj σ).toMonoidHom.comp (primeLocalToGlobal q))) =
      PlaceDecomp.decomp ℚ K w ⊓ (E.comap (IsScalarTower.toAlgHom ℚ K (AlgebraicClosure ℚ))).fixingSubgroup :=
  map_comap_fixingSubgroup_eq_of_forall_mem_iff (q : ℕ) K w σ hσ E hE

private theorem exists_forall_mem_iff_of_fixed' (L : Type) [Field L] [NumberField L] [Algebra L (AlgebraicClosure ℚ)]
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    ∃ v : HeightOneSpectrum (𝓞 L),
      ∀ x : L, algebraMap L (AlgebraicClosure ℚ) x ∈ σ • padicPlace q ↔ v.valuation L x ≤ 1 :=
  exists_forall_mem_iff_of_fixed (q : ℕ) L σ

private theorem exists_forall_mem_iff' [IsGalois ℚ K] (hw : ((q : ℕ) : 𝓞 K) ∈ w.asIdeal) :
    ∃ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      ∀ x : K, algebraMap K (AlgebraicClosure ℚ) x ∈ σ • padicPlace q ↔ w.valuation K x ≤ 1 :=
  exists_forall_mem_iff (q : ℕ) K w hw

end PlaceConjugate
p2m_reactivate "P2MW.S_groupCohomology_eq_zero_of_forall_continuousH2Map_primeLocal_eq_zero_pPrimary_continuousH2Sr_sUnitsMax.PlaceConjugate"
end
p2m_reactivate "P2MW.S_groupCohomology_eq_zero_of_forall_continuousH2Map_primeLocal_eq_zero_pPrimary_continuousH2Sr_sUnitsMax.PlaceConjugate"

section

p2m_open "groupCohomology P2MW.S_groupCohomology_eq_zero_of_forall_continuousH2Map_primeLocal_eq_zero_pPrimary_continuousH2Sr_sUnitsMax.groupCohomology"

namespace HasseGlue

private theorem exists_isLevelConstant_of_continuousH2Map_eq_zero
    {k G Gq : Type} [CommRing k] [Group G] [Group Gq]
    (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (S : Finset Nat.Primes) (M : Rep k G)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hF : F.IsUnramifiedOutside S) [Normal ℚ F]
    (f : cocycles₂ (M.quotientToInvariants (F.fixingSubgroup.comap r))) (lam : Gq →* G)
    (rG : Gq →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (hrG : ∀ g, r (lam g) = rG g)
    (hloc : continuousH2Map (rH := r) (rG := rG) lam hrG (A := M) (B := Rep.res lam M)
        LinearMap.id (fun _ _ => rfl)
        (continuousH2SrToContinuousH2 r S M (continuousH2SrInflation r S M F hF (H2π _ f))) = 0) :
    ∃ c : Gq → M, IsLevelConstant₁ rG c ∧
      ∀ g h : Gq,
        ((f ((lam g : G ⧸ F.fixingSubgroup.comap r), (lam h : G ⧸ F.fixingSubgroup.comap r)) :
            M.quotientToInvariants (F.fixingSubgroup.comap r)) : M)
          = M.ρ (lam g) (c h) - c (g * h) + c g := by
  rw [continuousH2SrInflation_H2π, continuousH2SrToContinuousH2_mk, continuousH2Map_continuousH2π,
    continuousH2π_eq_zero_iff, coe_levelCocycles₂Map, mem_levelCoboundaries₂_iff] at hloc
  obtain ⟨c, hc, hdc⟩ := hloc
  exact ⟨c, hc, fun g h => (congrFun hdc (g, h)).symm⟩

end HasseGlue
p2m_reactivate "P2MW.S_groupCohomology_eq_zero_of_forall_continuousH2Map_primeLocal_eq_zero_pPrimary_continuousH2Sr_sUnitsMax.PlaceConjugate"
end
p2m_reactivate "P2MW.S_groupCohomology_eq_zero_of_forall_continuousH2Map_primeLocal_eq_zero_pPrimary_continuousH2Sr_sUnitsMax.PlaceConjugate"

section

p2m_open "groupCohomology P2MW.S_groupCohomology_eq_zero_of_forall_continuousH2Map_primeLocal_eq_zero_pPrimary_continuousH2Sr_sUnitsMax.groupCohomology IntermediateField"

namespace HasseGlue

private theorem exists_normal_of_isLevelConstant₁
    {Gq : Type} [Group Gq] (ρ : Gq →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (c : Gq → AlgebraicClosure ℚ) (hc : IsLevelConstant₁ ρ c) :
    ∃ N : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ N ∧ Normal ℚ N ∧
      ∀ g s : Gq, ρ s ∈ N.fixingSubgroup → c (g * s) = c g := by
  haveI hnormal : Normal ℚ (AlgebraicClosure ℚ) := inferInstance
  obtain ⟨F', hF'fin, hF'⟩ := hc
  haveI : FiniteDimensional ℚ F' := hF'fin
  exact ⟨normalClosure ℚ F' (AlgebraicClosure ℚ), normalClosure.is_finiteDimensional ℚ F' (AlgebraicClosure ℚ),
    normalClosure.normal ℚ F' (AlgebraicClosure ℚ),
    fun g s hs => hF' g s (fixingSubgroup_antitone (le_normalClosure F') hs)⟩

private theorem finite_range_of_forall_mem_fixingSubgroup
    {Gq : Type} [Group Gq] (ρ : Gq →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (c : Gq → AlgebraicClosure ℚ) (N : IntermediateField ℚ (AlgebraicClosure ℚ)) (hNfin : FiniteDimensional ℚ N)
    (hNnormal : Normal ℚ N) (hcN : ∀ g s : Gq, ρ s ∈ N.fixingSubgroup → c (g * s) = c g) :
    (Set.range c).Finite := by
  classical
  haveI : FiniteDimensional ℚ N := hNfin
  haveI : Normal ℚ N := hNnormal
  let π : Gq → (N ≃ₐ[ℚ] N) := fun g => AlgEquiv.restrictNormalHom N (ρ g)
  have hπ : ∀ g g' : Gq, π g = π g' → c g' = c g := by
    intro g g' h
    have hmem : ρ (g⁻¹ * g') ∈ N.fixingSubgroup := by
      rw [← @IntermediateField.restrictNormalHom_ker ℚ (AlgebraicClosure ℚ) _ _ _ N hNnormal, MonoidHom.mem_ker,
        map_mul, map_inv, map_mul, map_inv]
      exact inv_mul_eq_one.mpr h
    simpa only [mul_inv_cancel_left] using hcN g (g⁻¹ * g') hmem
  refine (Set.finite_range fun τ : N ≃ₐ[ℚ] N => c (Function.invFun π τ)).subset ?_
  rintro _ ⟨g, rfl⟩
  exact ⟨π g, hπ g (Function.invFun π (π g)) (Function.invFun_eq (f := π) ⟨g, rfl⟩).symm⟩

private theorem exists_normal_level_of_isLevelConstant₁
    {Gq : Type} [Group Gq] (ρ : Gq →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (F₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ F₀]
    (c : Gq → AlgebraicClosure ℚ) (hc : IsLevelConstant₁ ρ c) :
    ∃ K : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ K ∧ Normal ℚ K ∧ F₀ ≤ K ∧
      (∀ g, c g ∈ K) ∧ ∀ g s : Gq, ρ s ∈ K.fixingSubgroup → c (g * s) = c g := by
  haveI hnormal : Normal ℚ (AlgebraicClosure ℚ) := inferInstance
  obtain ⟨N, hNfin, hNnormal, hcN⟩ := exists_normal_of_isLevelConstant₁ ρ c hc
  haveI : FiniteDimensional ℚ N := hNfin
  have hV : (Set.range c).Finite := finite_range_of_forall_mem_fixingSubgroup ρ c N hNfin hNnormal hcN
  haveI : Finite (Set.range c) := hV.to_subtype
  haveI : FiniteDimensional ℚ (adjoin ℚ (Set.range c)) := finiteDimensional_adjoin fun x _ => hnormal.isIntegral x
  obtain ⟨K₀, hK₀fin, hF₀K₀, hNK₀, hcK₀⟩ : ∃ K₀ : IntermediateField ℚ (AlgebraicClosure ℚ),
      FiniteDimensional ℚ K₀ ∧ F₀ ≤ K₀ ∧ N ≤ K₀ ∧ ∀ g, c g ∈ K₀ :=
    ⟨F₀ ⊔ N ⊔ adjoin ℚ (Set.range c), inferInstance, le_sup_left.trans le_sup_left, le_sup_right.trans le_sup_left,
      fun g => SetLike.le_def.mp le_sup_right (subset_adjoin ℚ (Set.range c) ⟨g, rfl⟩)⟩
  haveI : FiniteDimensional ℚ K₀ := hK₀fin
  refine ⟨normalClosure ℚ K₀ (AlgebraicClosure ℚ), normalClosure.is_finiteDimensional ℚ K₀ (AlgebraicClosure ℚ),
    normalClosure.normal ℚ K₀ (AlgebraicClosure ℚ), hF₀K₀.trans (le_normalClosure K₀),
    fun g => SetLike.le_def.mp (le_normalClosure K₀) (hcK₀ g), fun g s hs => ?_⟩
  exact hcN g s (fixingSubgroup_antitone (hNK₀.trans (le_normalClosure K₀)) hs)

end HasseGlue
p2m_reactivate "P2MW.S_groupCohomology_eq_zero_of_forall_continuousH2Map_primeLocal_eq_zero_pPrimary_continuousH2Sr_sUnitsMax.PlaceConjugate"
end
p2m_reactivate "P2MW.S_groupCohomology_eq_zero_of_forall_continuousH2Map_primeLocal_eq_zero_pPrimary_continuousH2Sr_sUnitsMax.PlaceConjugate"

section

p2m_open "IsDedekindDomain NumberField P2MW.S_groupCohomology_eq_zero_of_forall_continuousH2Map_primeLocal_eq_zero_pPrimary_continuousH2Sr_sUnitsMax.NumberField NumberField.PlaceDecomp P2MW.S_groupCohomology_eq_zero_of_forall_continuousH2Map_primeLocal_eq_zero_pPrimary_continuousH2Sr_sUnitsMax.NumberField.PlaceDecomp"
p2m_open_scoped "NumberField.PlaceDecomp P2MW.S_groupCohomology_eq_zero_of_forall_continuousH2Map_primeLocal_eq_zero_pPrimary_continuousH2Sr_sUnitsMax.NumberField.PlaceDecomp"

namespace HasseGlue

variable {E K : Type} [Field E] [Field K] [NumberField K] [Algebra E K] {w : HeightOneSpectrum (𝓞 K)}

private theorem decomp_smul_algebraMap (σ : decomp E K w) (x : K) :
    σ • algebraMap K (w.adicCompletion K) x = algebraMap K (w.adicCompletion K) ((σ : K ≃ₐ[E] K) x) := by
  rw [smul_def]
  exact actRingEquiv_coe σ (WithVal.toVal (w.valuation K) x)

private theorem ofMulDistribMulAction_ρ_ofMul_map_algebraMap (σ : decomp E K w) (u : Kˣ) :
    (Rep.ofMulDistribMulAction (decomp E K w) (w.adicCompletion K)ˣ).ρ σ
        (Additive.ofMul (Units.map (algebraMap K (w.adicCompletion K)).toMonoidHom u)) =
      Additive.ofMul (Units.map (algebraMap K (w.adicCompletion K)).toMonoidHom
        (Units.map (MonoidHomClass.toMonoidHom (σ : K ≃ₐ[E] K)) u)) := by
  rw [Rep.ofMulDistribMulAction_ρ_apply_apply]
  congr 1
  refine Units.ext ?_
  rw [coe_smul_units]
  exact decomp_smul_algebraMap σ u

private theorem exists_forall_eq_smul_sub_add_of_surjective
    {Gq D A : Type} [Group Gq] [Group D] [AddCommGroup A] (act : D → A → A)
    (res : Gq →* D) (hres : Function.Surjective res) (c : Gq → A)
    (hc : ∀ g s : Gq, res s = 1 → c (g * s) = c g) (F : D × D → A)
    (hF : ∀ g h : Gq, F (res g, res h) = act (res g) (c h) - c (g * h) + c g) :
    ∃ y : D → A, ∀ δ ε : D, F (δ, ε) = act δ (y ε) - y (δ * ε) + y δ := by
  have key : ∀ g g' : Gq, res g = res g' → c g = c g' := by
    intro g g' h
    have hs : res (g⁻¹ * g') = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
    simpa only [mul_inv_cancel_left] using (hc g (g⁻¹ * g') hs).symm
  refine ⟨fun δ => c (Function.surjInv hres δ), fun δ ε => ?_⟩
  obtain ⟨g, rfl⟩ := hres δ
  obtain ⟨h, rfl⟩ := hres ε
  rw [hF g h, key h (Function.surjInv hres (res h)) (Function.surjInv_eq hres (res h)).symm,
    key g (Function.surjInv hres (res g)) (Function.surjInv_eq hres (res g)).symm,
    key (g * h) (Function.surjInv hres (res g * res h)) (by rw [Function.surjInv_eq hres, map_mul])]

private theorem ofMul_mul_inv_mul {α : Type} [Group α] (a b c : α) :
    Additive.ofMul (a * b⁻¹ * c) = Additive.ofMul a - Additive.ofMul b + Additive.ofMul c := by
  rw [ofMul_mul, ofMul_mul, ofMul_inv, sub_eq_add_neg]

private theorem exists_forall_ofMul_map_eq_ρ_sub_add_of_surjective
    {E K K'' : Type} [Field E] [Field K] [Field K''] [NumberField K''] [Algebra E K''] [Algebra K K'']
    (w'' : IsDedekindDomain.HeightOneSpectrum (𝓞 K'')) {Gq : Type} [Group Gq]
    (res : Gq →* decomp E K'' w'') (hres : Function.Surjective res) (c₁ : Gq → K''ˣ)
    (hc : ∀ g s : Gq, res s = 1 → c₁ (g * s) = c₁ g) (F₀ : decomp E K'' w'' × decomp E K'' w'' → Kˣ)
    (hF : ∀ g h : Gq, Units.map (algebraMap K K'').toMonoidHom (F₀ (res g, res h)) =
      Units.map (MonoidHomClass.toMonoidHom ((res g : decomp E K'' w'') : K'' ≃ₐ[E] K'')) (c₁ h) *
        (c₁ (g * h))⁻¹ * c₁ g) :
    ∃ y : decomp E K'' w'' →
        Rep.ofMulDistribMulAction (decomp E K'' w'') (w''.adicCompletion K'')ˣ,
      ∀ g h : decomp E K'' w'',
        Additive.ofMul (Units.map (algebraMap K'' (w''.adicCompletion K'')).toMonoidHom
            (Units.map (algebraMap K K'').toMonoidHom (F₀ (g, h)))) =
          (Rep.ofMulDistribMulAction (decomp E K'' w'') (w''.adicCompletion K'')ˣ).ρ g (y h) - y (g * h) + y g := by
  refine exists_forall_eq_smul_sub_add_of_surjective
    (fun δ a => (Rep.ofMulDistribMulAction (decomp E K'' w'') (w''.adicCompletion K'')ˣ).ρ δ a) res hres
    (fun g => Additive.ofMul (Units.map (algebraMap K'' (w''.adicCompletion K'')).toMonoidHom (c₁ g)))
    (fun g s hs => by simp only [hc g s hs])
    (fun p => Additive.ofMul (Units.map (algebraMap K'' (w''.adicCompletion K'')).toMonoidHom
      (Units.map (algebraMap K K'').toMonoidHom (F₀ p)))) (fun g h => ?_)
  beta_reduce
  rw [hF g h, map_mul, map_mul, map_inv, ofMulDistribMulAction_ρ_ofMul_map_algebraMap]
  exact ofMul_mul_inv_mul (α := (w''.adicCompletion K'')ˣ) _ _ _

end HasseGlue
p2m_reactivate "P2MW.S_groupCohomology_eq_zero_of_forall_continuousH2Map_primeLocal_eq_zero_pPrimary_continuousH2Sr_sUnitsMax.PlaceConjugate"
end
p2m_reactivate "P2MW.S_groupCohomology_eq_zero_of_forall_continuousH2Map_primeLocal_eq_zero_pPrimary_continuousH2Sr_sUnitsMax.PlaceConjugate"

namespace HasseAsm

private theorem smooth {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) (m : sUnitsMaxRep S L) :
    ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧
      ∀ s : ↥L.fixingSubgroup, L.fixingSubgroup.subtype s ∈ F.fixingSubgroup → (sUnitsMaxRep S L).ρ s m = m := by
  obtain ⟨F, hF, hconst⟩ := (sUnitsMaxRep_smooth_and_divisible S hpS L).1 m
  refine ⟨F, hF, fun s hs => ?_⟩
  have h := hconst 1 s hs
  simpa only [one_mul, map_one, Module.End.one_apply] using h

private theorem exists_normal_level_ge (S : Finset Nat.Primes) (L F : IntermediateField ℚ (AlgebraicClosure ℚ))
    (hL : L.IsUnramifiedOutside S) (hF : F.IsUnramifiedOutside S) :
    ∃ F₁ : IntermediateField ℚ (AlgebraicClosure ℚ), F ≤ F₁ ∧ L ≤ F₁ ∧ F₁.IsUnramifiedOutside S ∧ Normal ℚ ↥F₁ := by
  obtain ⟨F₁, hle, hF₁, hnormal⟩ := IntermediateField.exists_normal_isUnramifiedOutside_of_le S (F ⊔ L) (hF.sup hL)
  exact ⟨F₁, le_sup_left.trans hle, le_sup_right.trans hle, hF₁, hnormal⟩

section valueForm

variable (S : Finset Nat.Primes) (L' F' : IntermediateField ℚ (AlgebraicClosure ℚ))

private theorem val_mem_sUnitsMax (x : sUnitsMaxRep S L') : sUnitsMaxRep.val S L' x ∈ sUnitsMax S :=
  sUnitsMaxStable_le S L' x.2

private theorem smul_val_eq_of_mem_invariants (hL'F' : L' ≤ F') [Normal ℚ ↥F']
    (x : (sUnitsMaxRep S L').quotientToInvariants (F'.fixingSubgroup.comap L'.fixingSubgroup.subtype))
    (s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hs : s ∈ F'.fixingSubgroup) :
    s • sUnitsMaxRep.val S L' (x : sUnitsMaxRep S L') = sUnitsMaxRep.val S L' (x : sUnitsMaxRep S L') := by
  have hsL' : s ∈ L'.fixingSubgroup := IntermediateField.fixingSubgroup_antitone hL'F' hs
  have h := x.2 ⟨⟨s, hsL'⟩, (Subgroup.mem_comap.2 hs)⟩
  rw [← sUnitsMaxRep.val_ρ S L' ⟨s, hsL'⟩ (x : sUnitsMaxRep S L')]
  exact congrArg (sUnitsMaxRep.val S L') h

private theorem mk_mul_eq_of_mem (g s : ↥L'.fixingSubgroup)
    (hs : (s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ F'.fixingSubgroup) :
    ((g * s : ↥L'.fixingSubgroup) : ↥L'.fixingSubgroup ⧸ F'.fixingSubgroup.comap L'.fixingSubgroup.subtype) =
      (g : ↥L'.fixingSubgroup ⧸ F'.fixingSubgroup.comap L'.fixingSubgroup.subtype) := by
  rw [QuotientGroup.eq]
  simp only [mul_inv_rev, inv_mul_cancel_right, Subgroup.mem_comap]
  first | exact (Subgroup.inv_mem_iff _).2 hs | simpa only [Subgroup.coe_subtype, Subgroup.coe_inv] using (Subgroup.inv_mem_iff _).2 hs

private theorem val_ρ_sub_add (g : ↥L'.fixingSubgroup) (u v w : sUnitsMaxRep S L') :
    sUnitsMaxRep.val S L' ((sUnitsMaxRep S L').ρ g u - v + w) =
      (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) • sUnitsMaxRep.val S L' u * (sUnitsMaxRep.val S L' v)⁻¹ *
        sUnitsMaxRep.val S L' w := by
  rw [← sUnitsMaxRep.val_ρ]
  rfl

end valueForm
p2m_reactivate "P2MW.S_groupCohomology_eq_zero_of_forall_continuousH2Map_primeLocal_eq_zero_pPrimary_continuousH2Sr_sUnitsMax.PlaceConjugate"

private theorem finiteIndex_image {p : ℕ} [Fact p.Prime] (L L' F' : IntermediateField ℚ (AlgebraicClosure ℚ))
    (hL'F' : L' ≤ F') [Normal ℚ ↥F'] (hcop : (L'.fixingSubgroup.relIndex L.fixingSubgroup).Coprime p) :
    ((L'.fixingSubgroup.subgroupOf L.fixingSubgroup).map
        (QuotientGroup.mk' (F'.fixingSubgroup.comap L.fixingSubgroup.subtype))).FiniteIndex := by
  refine ⟨?_⟩
  rw [HasseSylowLevel.index_map_mk'_eq_relIndex L L' F' hL'F']
  rintro h0
  rw [h0, Nat.coprime_zero_left] at hcop
  exact (Fact.out : p.Prime).ne_one hcop

end HasseAsm
p2m_reactivate "P2MW.S_groupCohomology_eq_zero_of_forall_continuousH2Map_primeLocal_eq_zero_pPrimary_continuousH2Sr_sUnitsMax.PlaceConjugate"

namespace HasseAsm

private theorem map_diag_H2π_eq_zero (p : ℕ) (hp : p.Prime) (S : Finset Nat.Primes)
    (L' F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hL'F : L' ≤ F) [FiniteDimensional ℚ ↥L']
    [FiniteDimensional ℚ ↥F]
    [Normal ℚ ↥F] [IsGalois ↥L' ↥(levelField L' F hL'F)] (hF : F.IsUnramifiedOutside S)
    (hG : IsPGroup p (↥L'.fixingSubgroup ⧸ F.fixingSubgroup.comap L'.fixingSubgroup.subtype))
    (h4 : p = 2 → ∃ i : ↥L', i ^ 2 = -1)
    (ι : (↥(levelField L' F hL'F) ≃ₐ[↥L'] ↥(levelField L' F hL'F)) →*
      (↥L'.fixingSubgroup ⧸ F.fixingSubgroup.comap L'.fixingSubgroup.subtype))
    (hι : Function.Injective ι)
    (φ : Rep.res ι ((sUnitsMaxRep S L').quotientToInvariants (F.fixingSubgroup.comap L'.fixingSubgroup.subtype)) ⟶
      NumberField.SUnits.sUnitsRep ↥L' ↥(levelField L' F hL'F) (placesOverPrimesFinset ↥L' S))
    (f₁ : cocycles₂ ((sUnitsMaxRep S L').quotientToInvariants (F.fixingSubgroup.comap L'.fixingSubgroup.subtype)))
    (hS : ∀ v : {v // v ∈ placesOverPrimesFinset ↥L' S},
      (groupCohomology.map (MonoidHom.id (↥(levelField L' F hL'F) ≃ₐ[↥L'] ↥(levelField L' F hL'F)))
          (GroupCohomology.RepPi.proj
            (NumberField.SIdele.fibre ↥L' ↥(levelField L' F hL'F) (placesOverPrimesFinset ↥L' S))
            (Sum.inl (Sum.inl v))) 2 ≫
        (groupCohomology.coindIso (NumberField.FiniteSIdele.localUnits ↥L' ↥(levelField L' F hL'F) v.1) 2).hom).hom
        ((groupCohomology.map (MonoidHom.id (↥(levelField L' F hL'F) ≃ₐ[↥L'] ↥(levelField L' F hL'F)))
            (NumberField.SIdele.diag ↥L' ↥(levelField L' F hL'F) (placesOverPrimesFinset ↥L' S)) 2).hom
          (H2π _ (mapCocycles₂ ι φ f₁))) = 0) :
    (groupCohomology.map ι
      (φ ≫ NumberField.SIdele.diag ↥L' ↥(levelField L' F hL'F) (placesOverPrimesFinset ↥L' S)) 2) (H2π _ f₁) = 0 := by

  have harch : p ≠ 2 ∧ IsPGroup p (↥(levelField L' F hL'F) ≃ₐ[↥L'] ↥(levelField L' F hL'F)) ∨
      ∃ i : ↥L', i ^ 2 = -1 := by
    by_cases hp2 : p = 2
    · exact Or.inr (h4 hp2)
    · exact Or.inl ⟨hp2, hG.of_injective ι hι⟩

  have hbij := NumberField.SIdele.bijective_groupCohomology_localCoordinates_of_ramificationIdx_eq_one ↥L'
    ↥(levelField L' F hL'F) (placesOverPrimesFinset ↥L' S)
    (LevelUnramified.hunr_of_isUnramifiedOutside S L' F hL'F hF) 1

  have hcomp : groupCohomology.map ι
      (φ ≫ NumberField.SIdele.diag ↥L' ↥(levelField L' F hL'F) (placesOverPrimesFinset ↥L' S)) 2 =
      groupCohomology.map ι φ 2 ≫ groupCohomology.map (MonoidHom.id _)
        (NumberField.SIdele.diag ↥L' ↥(levelField L' F hL'F) (placesOverPrimesFinset ↥L' S)) 2 := by
    have h := groupCohomology.map_comp ι (MonoidHom.id (↥(levelField L' F hL'F) ≃ₐ[↥L'] ↥(levelField L' F hL'F))) φ
      (NumberField.SIdele.diag ↥L' ↥(levelField L' F hL'F) (placesOverPrimesFinset ↥L' S)) 2
    exact h
  rw [hcomp, ModuleCat.comp_apply, H2π_comp_map_apply]
  exact CrepdCoord.eq_zero_of_forall_localCoordinate_eq_zero ↥L' ↥(levelField L' F hL'F) (placesOverPrimesFinset ↥L' S)
    hbij _ hS (fun v => CrepdArch.eq_zero_of_localUnits ↥L' ↥(levelField L' F hL'F) p hp harch v 1 _)

end HasseAsm
p2m_reactivate "P2MW.S_groupCohomology_eq_zero_of_forall_continuousH2Map_primeLocal_eq_zero_pPrimary_continuousH2Sr_sUnitsMax.PlaceConjugate"

section
p2m_open "IsDedekindDomain NumberField P2MW.S_groupCohomology_eq_zero_of_forall_continuousH2Map_primeLocal_eq_zero_pPrimary_continuousH2Sr_sUnitsMax.NumberField"
p2m_open_scoped "NumberField.PlaceDecomp P2MW.S_groupCohomology_eq_zero_of_forall_continuousH2Map_primeLocal_eq_zero_pPrimary_continuousH2Sr_sUnitsMax.NumberField.PlaceDecomp"

namespace HasseAsm

set_option maxHeartbeats 4000000 in

private theorem local_block (S : Finset Nat.Primes) (L L' F : IntermediateField ℚ (AlgebraicClosure ℚ))
    (hL'F : L' ≤ F) [FiniteDimensional ℚ ↥L'] [FiniteDimensional ℚ ↥F] [Normal ℚ ↥F]
    [Normal ↥L' ↥(levelField L' F hL'F)] (hF : F.IsUnramifiedOutside S)
    (a : continuousH2Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L))
    (hloc : ∀ (q : ↥S) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
      continuousH2Map
          (rH := L.fixingSubgroup.subtype)
          (rG := (((MulAut.conj σ).toMonoidHom.comp (primeLocalToGlobal (q : Nat.Primes))).comp
                    (L.fixingSubgroup.comap ((MulAut.conj σ).toMonoidHom.comp (primeLocalToGlobal (q : Nat.Primes)))).subtype))
          (((MulAut.conj σ).toMonoidHom.comp (primeLocalToGlobal (q : Nat.Primes))).subgroupComap L.fixingSubgroup)
          (fun _ => rfl)
          (A := sUnitsMaxRep S L)
          (B := Rep.res (((MulAut.conj σ).toMonoidHom.comp (primeLocalToGlobal (q : Nat.Primes))).subgroupComap L.fixingSubgroup) (sUnitsMaxRep S L))
          LinearMap.id (fun _ _ => rfl)
        (continuousH2SrToContinuousH2 L.fixingSubgroup.subtype S (sUnitsMaxRep S L) a) = 0)
    (f : cocycles₂ ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype)))
    (hf : continuousH2SrInflation L.fixingSubgroup.subtype S (sUnitsMaxRep S L) F hF (H2π _ f) = a)
    (hΓ : L'.fixingSubgroup ≤ L.fixingSubgroup)
    (ι : (↥(levelField L' F hL'F) ≃ₐ[↥L'] ↥(levelField L' F hL'F)) →*
      (↥L'.fixingSubgroup ⧸ F.fixingSubgroup.comap L'.fixingSubgroup.subtype))
    (hιg : ∀ g : ↥L'.fixingSubgroup,
      ι (levelGal L' F hL'F g) = (g : ↥L'.fixingSubgroup ⧸ F.fixingSubgroup.comap L'.fixingSubgroup.subtype))
    (φ : Rep.res ι ((sUnitsMaxRep S L').quotientToInvariants (F.fixingSubgroup.comap L'.fixingSubgroup.subtype)) ⟶
      NumberField.SUnits.sUnitsRep ↥L' ↥(levelField L' F hL'F) (placesOverPrimesFinset ↥L' S))
    (hφval : ∀ x,
      ((NumberField.SUnits.val ↥L' ↥(levelField L' F hL'F) (placesOverPrimesFinset ↥L' S) (φ.hom x) :
          ↥(levelField L' F hL'F)) : AlgebraicClosure ℚ)
        = ((sUnitsMaxRep.val S L' (x.1 : sUnitsMaxRep S L') : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ))
    (v : {v // v ∈ placesOverPrimesFinset ↥L' S}) :
    ∃ (K'' : Type) (_ : Field K'') (_ : NumberField K'') (_ : Algebra ↥L' K'')
      (_ : Algebra ↥(levelField L' F hL'F) K'')
      (_ : IsScalarTower ↥L' ↥(levelField L' F hL'F) K'') (_ : IsGalois ↥L' K'') (w'' : HeightOneSpectrum (𝓞 K''))
      (_ : HeightOneSpectrum.under (𝓞 ↥(levelField L' F hL'F)) w'' = PlaceAbove.above ↥L' ↥(levelField L' F hL'F) v.1)
      (y : PlaceDecomp.decomp ↥L' K'' w'' →
        Rep.ofMulDistribMulAction (PlaceDecomp.decomp ↥L' K'' w'') (w''.adicCompletion K'')ˣ),
      ∀ g h : PlaceDecomp.decomp ↥L' K'' w'',
        Additive.ofMul (Units.map (algebraMap K'' (w''.adicCompletion K'')).toMonoidHom
            (Units.map (algebraMap ↥(levelField L' F hL'F) K'').toMonoidHom
              (SUnits.val ↥L' ↥(levelField L' F hL'F) (placesOverPrimesFinset ↥L' S)
                ((mapCocycles₂ ι φ (LevelRestriction.resLevel S L L' hΓ F f))
                  (AlgEquiv.restrictNormalHom ↥(levelField L' F hL'F) (g : K'' ≃ₐ[↥L'] K''),
                    AlgEquiv.restrictNormalHom ↥(levelField L' F hL'F) (h : K'' ≃ₐ[↥L'] K'')))))) =
          (Rep.ofMulDistribMulAction (PlaceDecomp.decomp ↥L' K'' w'') (w''.adicCompletion K'')ˣ).ρ g (y h) -
            y (g * h) + y g := by

  obtain ⟨q, hqS, hqv⟩ : ∃ q ∈ S, ((q : ℕ) : 𝓞 ↥L') ∈ v.1.asIdeal := (mem_placesOverPrimesFinset ↥L' S v.1).1 v.2
  haveI : Fact (q : ℕ).Prime := ⟨q.2⟩
  letI : Algebra ℚ ↥(levelField L' F hL'F) := DivisionRing.toRatAlgebra
  haveI := HasseLevelFurniture.isScalarTower_rat_levelField_algClosure L' F hL'F
  haveI := HasseLevelFurniture.normal_rat_levelField L' F hL'F
  haveI : IsGalois ℚ ↥(levelField L' F hL'F) := ⟨⟩
  have hw : ((q : ℕ) : 𝓞 ↥(levelField L' F hL'F)) ∈ (PlaceAbove.above ↥L' ↥(levelField L' F hL'F) v.1).asIdeal := by
    rw [← PlaceAbove.comap_above ↥L' ↥(levelField L' F hL'F) v.1, Ideal.mem_comap, map_natCast] at hqv
    exact hqv
  have hσex := PlaceConjugate.exists_forall_mem_iff' q ↥(levelField L' F hL'F)
    (PlaceAbove.above ↥L' ↥(levelField L' F hL'F) v.1) hw
  obtain ⟨σ, hσK⟩ := hσex

  have hloc' := hloc ⟨q, hqS⟩ σ
  rw [← hf] at hloc'
  have hdesc := HasseGlue.exists_isLevelConstant_of_continuousH2Map_eq_zero L.fixingSubgroup.subtype S
    (sUnitsMaxRep S L) F hF f
    (((MulAut.conj σ).toMonoidHom.comp (primeLocalToGlobal q)).subgroupComap L.fixingSubgroup)
    (((MulAut.conj σ).toMonoidHom.comp (primeLocalToGlobal q)).comp
      (L.fixingSubgroup.comap ((MulAut.conj σ).toMonoidHom.comp (primeLocalToGlobal q))).subtype)
    (fun _ => rfl) hloc'
  obtain ⟨c, hc, hcf⟩ := hdesc

  have hcval : IsLevelConstant₁
      ((((MulAut.conj σ).toMonoidHom.comp (primeLocalToGlobal (q : Nat.Primes))).comp
        (L.fixingSubgroup.comap ((MulAut.conj σ).toMonoidHom.comp (primeLocalToGlobal (q : Nat.Primes)))).subtype))
      (fun g => ((sUnitsMaxRep.val S L (c g) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ)) :=
    hc.imp fun N hN => ⟨hN.1, fun g s hs =>
      congrArg (fun m => ((sUnitsMaxRep.val S L m : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ)) (hN.2 g s hs)⟩
  have hKex := HasseGlue.exists_normal_level_of_isLevelConstant₁ _ F _ hcval
  obtain ⟨Kbig, hKfin, hKnormal, hFK, hcmem, hcconst⟩ := hKex
  haveI := hKfin
  haveI := hKnormal
  have hL'K : L' ≤ Kbig := hL'F.trans hFK

  letI : Algebra ℚ ↥(levelField L' Kbig hL'K) := DivisionRing.toRatAlgebra
  haveI := HasseLevelFurniture.isScalarTower_rat_levelField_algClosure L' Kbig hL'K
  haveI := HasseLevelFurniture.normal_rat_levelField L' Kbig hL'K
  haveI := HasseLevelFurniture.isScalarTower_rat_base_levelField L' Kbig hL'K
  haveI hGalK'' : IsGalois ↥L' ↥(levelField L' Kbig hL'K) := HasseLevelFurniture.isGalois_levelField L' Kbig hL'K
  letI := HasseLevelFurniture.levelAlgebra L' F Kbig hL'F hL'K hFK
  haveI := HasseLevelFurniture.levelAlgebra_isScalarTower L' F Kbig hL'F hL'K hFK
  haveI := HasseLevelFurniture.levelAlgebra_isScalarTower_algClosure L' F Kbig hL'F hL'K hFK

  have hwex := PlaceConjugate.exists_forall_mem_iff_of_fixed' q ↥(levelField L' Kbig hL'K) σ
  obtain ⟨w'', hσ''⟩ := hwex
  have hunder : HeightOneSpectrum.under (𝓞 ↥(levelField L' F hL'F)) w'' =
      PlaceAbove.above ↥L' ↥(levelField L' F hL'F) v.1 := by
    exact PlaceConjugate.under_eq_of_forall_mem_iff _ _ _ _ hσK w'' hσ''

  have hrange : ((AlgEquiv.restrictNormalHom ↥(levelField L' Kbig hL'K)).comp
        ((MulAut.conj σ).toMonoidHom.comp (primeLocalToGlobal q))).range =
      PlaceDecomp.decomp ℚ ↥(levelField L' Kbig hL'K) w'' := by
    exact PlaceConjugate.range_eq_decomp_of_forall_mem_iff' q ↥(levelField L' Kbig hL'K) w'' σ hσ''
  have hE : L' ≤ (IsScalarTower.toAlgHom ℚ ↥(levelField L' Kbig hL'K) (AlgebraicClosure ℚ)).fieldRange := by
    intro x hx
    exact ⟨levelFieldEquiv L' Kbig hL'K ⟨x, hL'K hx⟩, rfl⟩
  have hmap : (L'.fixingSubgroup.comap ((MulAut.conj σ).toMonoidHom.comp (primeLocalToGlobal q))).map
        ((AlgEquiv.restrictNormalHom ↥(levelField L' Kbig hL'K)).comp
          ((MulAut.conj σ).toMonoidHom.comp (primeLocalToGlobal q))) =
      PlaceDecomp.decomp ℚ ↥(levelField L' Kbig hL'K) w'' ⊓
        (L'.comap (IsScalarTower.toAlgHom ℚ ↥(levelField L' Kbig hL'K) (AlgebraicClosure ℚ))).fixingSubgroup := by
    exact PlaceConjugate.map_comap_fixingSubgroup_eq_of_forall_mem_iff' q ↥(levelField L' Kbig hL'K) w'' σ hσ'' L' hE
  have hsurj : Function.Surjective (HasseLevelFurniture.resHom L' Kbig hL'K q σ w'' hrange) := by
    exact HasseLevelFurniture.resHom_surjective L' Kbig hL'K q σ w'' hrange hmap

  let jD : ↥(L'.fixingSubgroup.comap ((MulAut.conj σ).toMonoidHom.comp (primeLocalToGlobal q))) →*
      ↥(L.fixingSubgroup.comap ((MulAut.conj σ).toMonoidHom.comp (primeLocalToGlobal q))) :=
    Subgroup.inclusion (Subgroup.comap_mono hΓ)
  let c₁ : ↥(L'.fixingSubgroup.comap ((MulAut.conj σ).toMonoidHom.comp (primeLocalToGlobal q))) →
      (↥(levelField L' Kbig hL'K))ˣ := fun d =>
    Units.mk0 (levelFieldEquiv L' Kbig hL'K ⟨_, hcmem (jD d)⟩) (by
      intro h0
      apply (sUnitsMaxRep.val S L (c (jD d))).ne_zero
      have h1 := congrArg (fun z : ↥(levelField L' Kbig hL'K) => (z : AlgebraicClosure ℚ)) h0
      simp only [coe_levelFieldEquiv, ZeroMemClass.coe_zero] at h1
      exact h1)

  have hc₁ : ∀ g s, HasseLevelFurniture.resHom L' Kbig hL'K q σ w'' hrange s = 1 → c₁ (g * s) = c₁ g := by
    intro g s hs
    have hfix := HasseLevelFurniture.mem_fixingSubgroup_of_resHom_eq_one L' Kbig hL'K q σ w'' hrange s hs
    apply Units.ext
    apply Subtype.ext
    simp only [c₁, Units.val_mk0, coe_levelFieldEquiv, map_mul]
    exact hcconst (jD g) (jD s) hfix

  have hF : ∀ g h, Units.map (algebraMap ↥(levelField L' F hL'F) ↥(levelField L' Kbig hL'K)).toMonoidHom
        (SUnits.val ↥L' ↥(levelField L' F hL'F) (placesOverPrimesFinset ↥L' S)
          ((mapCocycles₂ ι φ (LevelRestriction.resLevel S L L' hΓ F f))
            (AlgEquiv.restrictNormalHom ↥(levelField L' F hL'F)
                (HasseLevelFurniture.resHom L' Kbig hL'K q σ w'' hrange g :
                  ↥(levelField L' Kbig hL'K) ≃ₐ[↥L'] ↥(levelField L' Kbig hL'K)),
              AlgEquiv.restrictNormalHom ↥(levelField L' F hL'F)
                (HasseLevelFurniture.resHom L' Kbig hL'K q σ w'' hrange h :
                  ↥(levelField L' Kbig hL'K) ≃ₐ[↥L'] ↥(levelField L' Kbig hL'K))))) =
      Units.map (MonoidHomClass.toMonoidHom
          (HasseLevelFurniture.resHom L' Kbig hL'K q σ w'' hrange g :
            ↥(levelField L' Kbig hL'K) ≃ₐ[↥L'] ↥(levelField L' Kbig hL'K))) (c₁ h) *
        (c₁ (g * h))⁻¹ * c₁ g := by
    intro g h
    have h1 := congrArg (fun m => ((sUnitsMaxRep.val S L m : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ))
      (hcf (jD g) (jD h))
    have h2 := HasseAsm.val_ρ_sub_add S L
      ((((MulAut.conj σ).toMonoidHom.comp (primeLocalToGlobal q)).subgroupComap L.fixingSubgroup) (jD g))
      (c (jD h)) (c (jD g * jD h)) (c (jD g))
    have h3 := h1.trans (congrArg Units.val h2)
    simp only [Units.val_mul, Units.val_inv_eq_inv_val] at h3
    have h5 : ∀ a b : ↥(levelField L' F hL'F) ≃ₐ[↥L'] ↥(levelField L' F hL'F),
        (mapCocycles₂ ι φ (LevelRestriction.resLevel S L L' hΓ F f)) (a, b) =
          φ.hom ((LevelRestriction.resLevel S L L' hΓ F f) (ι a, ι b)) :=
      fun _ _ => rfl
    apply Units.ext
    apply Subtype.ext
    simp only [Units.coe_map, MonoidHom.coe_coe, Units.val_mul, Units.val_inv_eq_inv_val, c₁, Units.val_mk0,
      HasseLevelFurniture.coe_resHom, HasseLevelFurniture.restrictNormalHom_levelGal, map_mul]
    rw [h5, hιg, hιg]
    push_cast
    simp only [levelGal_apply_coe, coe_levelFieldEquiv]
    exact (hφval ((LevelRestriction.resLevel S L L' hΓ F f)
      ((HasseLevelFurniture.lamE L' q σ g : ↥L'.fixingSubgroup ⧸ F.fixingSubgroup.comap L'.fixingSubgroup.subtype),
        (HasseLevelFurniture.lamE L' q σ h :
          ↥L'.fixingSubgroup ⧸ F.fixingSubgroup.comap L'.fixingSubgroup.subtype)))).trans h3
  refine ⟨↥(levelField L' Kbig hL'K), inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    hGalK'', w'', hunder, ?_⟩
  exact HasseGlue.exists_forall_ofMul_map_eq_ρ_sub_add_of_surjective w''
    (HasseLevelFurniture.resHom L' Kbig hL'K q σ w'' hrange) hsurj c₁ hc₁
    (fun gh => SUnits.val ↥L' ↥(levelField L' F hL'F) (placesOverPrimesFinset ↥L' S)
      ((mapCocycles₂ ι φ (LevelRestriction.resLevel S L L' hΓ F f))
        (AlgEquiv.restrictNormalHom ↥(levelField L' F hL'F)
            (gh.1 : ↥(levelField L' Kbig hL'K) ≃ₐ[↥L'] ↥(levelField L' Kbig hL'K)),
          AlgEquiv.restrictNormalHom ↥(levelField L' F hL'F)
            (gh.2 : ↥(levelField L' Kbig hL'K) ≃ₐ[↥L'] ↥(levelField L' Kbig hL'K)))))
    hF

end HasseAsm
p2m_reactivate "P2MW.S_groupCohomology_eq_zero_of_forall_continuousH2Map_primeLocal_eq_zero_pPrimary_continuousH2Sr_sUnitsMax.PlaceConjugate"

end
p2m_reactivate "P2MW.S_groupCohomology_eq_zero_of_forall_continuousH2Map_primeLocal_eq_zero_pPrimary_continuousH2Sr_sUnitsMax.PlaceConjugate"

theorem solution
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hL : L.IsUnramifiedOutside S) [FiniteDimensional ℚ ↥L]
    (h4 : p = 2 → ∃ i ∈ L, i ^ 2 = -1)
    (a : continuousH2Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L))
    (ha : a ∈ Submodule.torsion' ℤ (continuousH2Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L)) (Submonoid.powers (p : ℤ)))
    (hloc : ∀ (q : ↥S) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
      continuousH2Map
          (rH := L.fixingSubgroup.subtype)
          (rG := (((MulAut.conj σ).toMonoidHom.comp (primeLocalToGlobal (q : Nat.Primes))).comp
                    (L.fixingSubgroup.comap ((MulAut.conj σ).toMonoidHom.comp (primeLocalToGlobal (q : Nat.Primes)))).subtype))
          (((MulAut.conj σ).toMonoidHom.comp (primeLocalToGlobal (q : Nat.Primes))).subgroupComap L.fixingSubgroup)
          (fun _ => rfl)
          (A := sUnitsMaxRep S L)
          (B := Rep.res (((MulAut.conj σ).toMonoidHom.comp (primeLocalToGlobal (q : Nat.Primes))).subgroupComap L.fixingSubgroup) (sUnitsMaxRep S L))
          LinearMap.id (fun _ _ => rfl)
        (continuousH2SrToContinuousH2 L.fixingSubgroup.subtype S (sUnitsMaxRep S L) a) = 0) :
    a = 0 := by

  have hsm : ∀ m : sUnitsMaxRep S L, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧
      ∀ s : ↥L.fixingSubgroup, L.fixingSubgroup.subtype s ∈ F.fixingSubgroup → (sUnitsMaxRep S L).ρ s m = m :=
    HasseAsm.smooth S hpS L

  obtain ⟨F₀, hF₀, hGal₀, y, hy⟩ :=
    exists_continuousH2SrInflation_eq L.fixingSubgroup.subtype S (sUnitsMaxRep S L) hsm a
  induction y using H2_induction_on with
  | h f₀ => ?_

  obtain ⟨F, hF₀F, hLF, hF, hnormF⟩ := HasseAsm.exists_normal_level_ge S L F₀ hL hF₀
  haveI : Normal ℚ ↥F := hnormF
  haveI : FiniteDimensional ℚ ↥F := hF.1
  haveI : IsGalois ℚ ↥F := ⟨⟩
  have hle : F.fixingSubgroup.comap L.fixingSubgroup.subtype ≤ F₀.fixingSubgroup.comap L.fixingSubgroup.subtype :=
    Subgroup.comap_mono (IntermediateField.fixingSubgroup_antitone hF₀F)
  obtain ⟨f, hf⟩ : ∃ f : cocycles₂ ((sUnitsMaxRep S L).quotientToInvariants
      (F.fixingSubgroup.comap L.fixingSubgroup.subtype)),
      continuousH2SrInflation L.fixingSubgroup.subtype S (sUnitsMaxRep S L) F hF (H2π _ f) = a :=
    ⟨InvariantsPullback.pullback (sUnitsMaxRep S L) _ _ hle f₀,
      (continuousH2SrInflation_H2pi_eq_of_le L.fixingSubgroup.subtype S (sUnitsMaxRep S L) F₀ F hF₀ hF f₀ _
        (fun g h => InvariantsPullback.coe_pullback_mk (sUnitsMaxRep S L) _ _ hle f₀ g h)).trans hy⟩

  obtain ⟨L', hLL', hL'F, hcop, hG⟩ := HasseSylowLevel.exists_sylowField p L F hLF
  haveI : FiniteDimensional ℚ ↥L' := (hF.of_le hL'F).1
  have hΓ : L'.fixingSubgroup ≤ L.fixingSubgroup := IntermediateField.fixingSubgroup_antitone hLL'

  haveI : Normal ↥L' ↥(levelField L' F hL'F) := (HasseLevelFurniture.isGalois_levelField L' F hL'F).to_normal
  obtain ⟨ι, hι, hιg, φ, hφ, hφval⟩ := CrepdPkg.exists_pkg S L' F hL'F
    (exists_addEquiv_quotientToInvariants_sUnitsMaxRep_sUnitsRep S L' F hL'F hF)
  haveI hGalK : IsGalois ↥L' ↥(levelField L' F hL'F) := HasseLevelFurniture.isGalois_levelField L' F hL'F
  have himg : (groupCohomology.map ι
      (φ ≫ NumberField.SIdele.diag ↥L' ↥(levelField L' F hL'F) (placesOverPrimesFinset ↥L' S)) 2)
      (H2π _ (LevelRestriction.resLevel S L L' hΓ F f)) = 0 :=
    HasseAsm.map_diag_H2π_eq_zero p Fact.out S L' F hL'F hF hG
      (fun hp2 => CrepdArch.exists_sq_eq_neg_one_of_le hLL' (h4 hp2)) ι hι.1 φ
      (LevelRestriction.resLevel S L L' hΓ F f)
      (fun v => NumberField.SIdele.localCoordinate_map_diag_H2π_eq_zero_of_exists_layer ↥L' ↥(levelField L' F hL'F)
        (placesOverPrimesFinset ↥L' S) (mapCocycles₂ ι φ (LevelRestriction.resLevel S L L' hΓ F f)) v
        (HasseAsm.local_block S L L' F hL'F hF a hloc f hf hΓ ι hιg φ hφval v))
  obtain ⟨F', hF', hGalF', hFF', y₁, hy₁⟩ :=
    exists_level_coboundary_of_isPGroup_of_map_diag_H2pi_eq_zero_sUnitsMaxRep p S ⟨pPrime p, hpS, rfl⟩ L' F hL'F hF hG
      ι hιg φ hφ hφval (LevelRestriction.resLevel S L L' hΓ F f) himg
  have hL'F' : L' ≤ F' := hL'F.trans hFF'

  obtain ⟨f', hff', hres⟩ :=
    HasseSylowKill.exists_cocycle_coe_eq_and_map_res_H2π_eq_zero S L L' F F' hLL' hL'F hFF' hΓ f
    (fun g => sUnitsMaxRep.val S L'
      (y₁ (g : ↥L'.fixingSubgroup ⧸ F'.fixingSubgroup.comap L'.fixingSubgroup.subtype) : sUnitsMaxRep S L'))
    (fun g => HasseAsm.val_mem_sUnitsMax S L' _)
    (fun g s hs => by
      dsimp only
      rw [HasseAsm.mk_mul_eq_of_mem L' F' g s hs])
    (fun g s hs => HasseAsm.smul_val_eq_of_mem_invariants S L' F' hL'F' _ s hs)
    (fun g h => by
      have h1 := congrArg (sUnitsMaxRep.val S L') (hy₁ g h)
      rw [HasseAsm.val_ρ_sub_add, LevelRestriction.val_resLevel] at h1
      exact h1)

  haveI := HasseAsm.finiteIndex_image (p := p) L L' F' hL'F' hcop
  obtain ⟨τ⟩ := Cores.Transversal.nonempty (H := (L'.fixingSubgroup.subgroupOf L.fixingSubgroup).map
    (QuotientGroup.mk' (F'.fixingSubgroup.comap L.fixingSubgroup.subtype)))
  have hcores := Cores.cores_map_res_eq_index_smul
    ((sUnitsMaxRep S L).quotientToInvariants (F'.fixingSubgroup.comap L.fixingSubgroup.subtype)) _ τ (H2π _ f')
  rw [hres, map_zero] at hcores

  have ha' : continuousH2SrInflation L.fixingSubgroup.subtype S (sUnitsMaxRep S L) F' hF' (H2π _ f') = a :=
    (continuousH2SrInflation_H2pi_eq_of_le L.fixingSubgroup.subtype S (sUnitsMaxRep S L) F F' hF hF' f f'
      hff').trans hf
  have hindex : ((L'.fixingSubgroup.subgroupOf L.fixingSubgroup).map
      (QuotientGroup.mk' (F'.fixingSubgroup.comap L.fixingSubgroup.subtype))).index • a = 0 := by
    rw [← ha', ← map_nsmul, ← hcores, map_zero]

  have hcop' : ((L'.fixingSubgroup.subgroupOf L.fixingSubgroup).map
      (QuotientGroup.mk' (F'.fixingSubgroup.comap L.fixingSubgroup.subtype))).index.Coprime p := by
    rw [HasseSylowLevel.index_map_mk'_eq_relIndex L L' F' hL'F']
    exact hcop
  exact PPrimarySylowReduction.eq_zero_of_pow_nsmul_eq_zero_of_coprime_nsmul_eq_zero
    (PPrimarySylowReduction.exists_pow_nsmul_eq_zero_of_mem_torsion'_powers ha) hcop' hindex

end S_groupCohomology_eq_zero_of_forall_continuousH2Map_primeLocal_eq_zero_pPrimary_continuousH2Sr_sUnitsMax
end P2MW
export P2MW.S_groupCohomology_eq_zero_of_forall_continuousH2Map_primeLocal_eq_zero_pPrimary_continuousH2Sr_sUnitsMax (solution)
