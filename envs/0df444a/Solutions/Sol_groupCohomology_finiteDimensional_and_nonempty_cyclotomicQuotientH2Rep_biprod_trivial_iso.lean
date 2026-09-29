-- Prove2me | solution 1 for groupCohomology.finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/e43108ef-582c-50c4-9bc3-b3764538cc60

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_NumberField_SelmerRepModP
import Definitions.Def_Rep_QuotientRightTranslation
import Definitions.Def_GroupCohomology_CyclotomicQuotientH2Rep
import Definitions.Def_NumberField_SUnitsMax
import Theorems.Thm_groupCohomology_exists_continuousH2Sr_cyclotomicQuotientRep_equiv_pin
import Theorems.Thm_groupCohomology_exists_kummerBrauer_maps_continuousH2Sr_cyclotomic_natural
import Theorems.Thm_NumberField_LevelArith_exists_continuousH1Sr_sUnitsMaxRep_linearMap_sClassGroupRep_injective_natural
import Theorems.Thm_NumberField_LevelArith_exists_continuousH1Sr_sUnitsMaxRep_linearMap_sClassGroupRep_injective
import Theorems.Thm_NumberField_LevelArith_exists_restrict_and_torsionBy_sClassGroupRep_linearEquiv_sClassTorsionP
import Theorems.Thm_NumberField_LevelArith_exists_placesAbove_inr_equiv_primesOver
import Theorems.Thm_Rep_nonempty_iso_biprod_of_shortExact_of_trivial_of_coprime
import Theorems.Thm_NumberField_LevelArith_nonempty_repTorsionP_iso_repModP
import Theorems.Thm_NumberField_LevelArith_sUnitsMaxStable_eq_sUnitsMax
import Theorems.Thm_IntermediateField_IsUnramifiedOutside_normalClosure
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso
p2m_attr_erase "instance" "M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete groupCohomology.normal_comap_fixingSubgroup groupCohomology.finiteIndex_comap_fixingSubgroup AlgebraicClosure.Rat.isGalois FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap NumberField.AdelicHaar.locallyCompactSpace_adeleRing NumberField.AdelicHaar.finite_residueField_adicCompletionIntegers NumberField.AdelicHaar.locallyCompactSpace_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_finiteAdeleRing NumberField.AdelicHaar.compactSpace_adicCompletionIntegers NumberField.AdelicHaar.t2Space_finiteAdeleRing NumberField.AdelicHaar.t2Space_matrix_adeleRing NumberField.AdelicHaar.t2Space_adeleRing NumberField.AdelicHaar.fact_isOpen_adicCompletionIntegers NumberField.AdelicHaar.t2Space_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_matrix_adeleRing NumberField.AdelicHaar.t2Space_infiniteAdeleRing NumberField.AdelicHaar.properSpace_adicCompletion ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal"
p2m_attr_erase "instance" "M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite Deep.NTSupply.instNormalRayClassSubgroup instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal"
p2m_attr_erase "simp" "M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk M4aHerbrand.IdeleGaloisDescent.classAct_mk M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq ExtCitation.LocalLevel.coe_smul_OO WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply groupCohomology.continuousH2Inflation_H2π groupCohomology.levelInflate₂_apply groupCohomology.coe_levelInflateCocycles₂ groupCohomology.levelInflate₁_apply M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply"
p2m_attr_erase "simp" "SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff"
p2m_attr_erase "simp" "RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl IsLocalRing.principalUnits_zero groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul"
p2m_attr_erase "simp" "M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply M4aHerbrand.Bridge.finiteConorm_apply M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Module CategoryTheory.Limits CategoryTheory.MonoidalCategory.Limits groupCohomology ExtCitation NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith"
p2m_open_scoped "Classical NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith TensorProduct"

set_option maxHeartbeats 1600000

namespace IntermediateField p2m_export "IntermediateField" "mk val lift inclusion fixingSubgroup_bot ext mem_fixingSubgroup_iff comap fixingSubgroup fieldRange_comp_val map_mono map_bot map normalClosure IsUnramifiedOutside IsUnramifiedOutside.of_le IsUnramifiedOutside.normalClosure" namespace IsUnramifiedOutside p2m_export "IntermediateField.IsUnramifiedOutside" "of_le normalClosure" end IntermediateField.IsUnramifiedOutside
namespace IntermediateField.IsUnramifiedOutside
p2m_open_scoped "IntermediateField IntermediateField.IsUnramifiedOutside" in

private theorem _root_.IntermediateField.IsUnramifiedOutside.map_algEquiv
    {S : Finset Nat.Primes} {F : IntermediateField ℚ (AlgebraicClosure ℚ)} (hF : F.IsUnramifiedOutside S)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    (F.map (σ : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ)).IsUnramifiedOutside S := by
  haveI : FiniteDimensional ℚ ↥F := hF.1
  refine IntermediateField.IsUnramifiedOutside.of_le ?_ (IntermediateField.IsUnramifiedOutside.normalClosure hF)
  rw [← IntermediateField.fieldRange_comp_val]
  exact AlgHom.fieldRange_le_normalClosure _

end IntermediateField.IsUnramifiedOutside
p2m_export "" "IntermediateField.IsUnramifiedOutside.map_algEquiv"
noncomputable section

namespace IsDedekindDomain
p2m_export "IsDedekindDomain" "HeightOneSpectrum.ext HeightOneSpectrum.valuation_of_mk' HeightOneSpectrum.intValuation_if_neg selmerGroup HeightOneSpectrum.equivOfRingEquiv mk HeightOneSpectrum"
namespace selmerGroup
p2m_export "IsDedekindDomain.selmerGroup" "valuation"
namespace K3aPf
p2m_open "IsDedekindDomain.selmerGroup IsDedekindDomain"

p2m_open "IsDedekindDomain P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.IsDedekindDomain FractionalIdeal"
open scoped nonZeroDivisors Classical

variable {R : Type} [CommRing R] [IsDedekindDomain R]

def comapPrime (σ : R ≃+* R) (v : HeightOneSpectrum R) : HeightOneSpectrum R where
  asIdeal := v.asIdeal.comap (σ : R →+* R)
  isPrime := Ideal.comap_isPrime _ _
  ne_bot := fun h => by
    have e : Ideal.map (σ : R →+* R) (v.asIdeal.comap (σ : R →+* R)) = v.asIdeal := Ideal.map_comap_of_surjective _ σ.surjective _
    rw [h, Ideal.map_bot] at e
    exact v.ne_bot e.symm

omit [IsDedekindDomain R] in
theorem map_comapPrime (σ : R ≃+* R) (v : HeightOneSpectrum R) :
    (comapPrime σ v).asIdeal.map (σ : R →+* R) = v.asIdeal :=
  Ideal.map_comap_of_surjective _ σ.surjective _

theorem map_dvd_map_iff (σ : R ≃+* R) (I J : Ideal R) : I.map (σ : R →+* R) ∣ J.map (σ : R →+* R) ↔ I ∣ J := by
  constructor
  · intro h
    have := Ideal.map_mono (f := (σ.symm : R →+* R)) (Ideal.le_of_dvd h)
    rw [Ideal.map_of_equiv, Ideal.map_of_equiv] at this
    exact Ideal.dvd_iff_le.2 this
  · intro h
    exact Ideal.dvd_iff_le.2 (Ideal.map_mono (Ideal.le_of_dvd h))

omit [IsDedekindDomain R] in
theorem map_ne_bot (σ : R ≃+* R) {I : Ideal R} (hI : I ≠ ⊥) : I.map (σ : R →+* R) ≠ ⊥ := fun h =>
  hI ((Ideal.map_eq_bot_iff_of_injective σ.injective).1 h)

theorem count_map (σ : R ≃+* R) (v : HeightOneSpectrum R) {I : Ideal R} (hI : I ≠ ⊥) :
    (Associates.mk v.asIdeal).count (Associates.mk (I.map (σ : R →+* R))).factors =
      (Associates.mk (comapPrime σ v).asIdeal).count (Associates.mk I).factors := by
  have hI' : Associates.mk (I.map (σ : R →+* R)) ≠ 0 := by rw [Ne, Associates.mk_eq_zero]; exact map_ne_bot σ hI
  have hI0 : Associates.mk I ≠ 0 := by rw [Ne, Associates.mk_eq_zero]; exact hI
  refine eq_of_forall_le_iff fun k => ?_
  rw [← Associates.prime_pow_dvd_iff_le hI' v.associates_irreducible, ← Associates.prime_pow_dvd_iff_le hI0 (comapPrime σ v).associates_irreducible,
    ← Associates.mk_pow, ← Associates.mk_pow, Associates.mk_le_mk_iff_dvd, Associates.mk_le_mk_iff_dvd, ← map_comapPrime σ v, ← Ideal.map_pow,
    map_dvd_map_iff]

end IsDedekindDomain.selmerGroup.K3aPf

end

noncomputable section

namespace IsDedekindDomain
p2m_export "IsDedekindDomain" "HeightOneSpectrum.ext HeightOneSpectrum.valuation_of_mk' HeightOneSpectrum.intValuation_if_neg selmerGroup HeightOneSpectrum.equivOfRingEquiv mk HeightOneSpectrum"
namespace selmerGroup
p2m_export "IsDedekindDomain.selmerGroup" "valuation"
namespace K3aPf
p2m_open "IsDedekindDomain.selmerGroup IsDedekindDomain"

p2m_open "IsDedekindDomain P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.IsDedekindDomain FractionalIdeal"
open scoped nonZeroDivisors Classical

variable {R : Type} [CommRing R] [IsDedekindDomain R] (K : Type) [Field K] [Algebra R K] [IsFractionRing R K]

theorem valuation_map_eq (σR : R ≃+* R) (σK : K ≃+* K) (hσ : ∀ r : R, σK (algebraMap R K r) = algebraMap R K (σR r))
    (v : HeightOneSpectrum R) (y : K) : v.valuation K (σK y) = (comapPrime σR v).valuation K y := by
  classical
  obtain ⟨⟨r, s⟩, hrs⟩ : ∃ q : R × R⁰, y * algebraMap R K q.2 = algebraMap R K q.1 := ⟨IsLocalization.sec R⁰ y, IsLocalization.sec_spec _ _⟩
  have hs0 : (s : R) ≠ 0 := nonZeroDivisors.ne_zero s.2
  have hσs : σR s ∈ R⁰ := mem_nonZeroDivisors_of_ne_zero (by simpa using hs0)
  have hy : y = IsLocalization.mk' K r s := by
    rw [IsLocalization.eq_mk'_iff_mul_eq]; exact hrs
  have hσy : σK y = IsLocalization.mk' K (σR r) ⟨σR s, hσs⟩ := by
    rw [IsLocalization.eq_mk'_iff_mul_eq]
    change σK y * algebraMap R K (σR s) = algebraMap R K (σR r)
    rw [← hσ, ← hσ, ← map_mul, hrs]
  rw [hσy, hy, HeightOneSpectrum.valuation_of_mk', HeightOneSpectrum.valuation_of_mk']

  have key : ∀ a : R, v.intValuation (σR a) = (comapPrime σR v).intValuation a := by
    intro a
    by_cases ha : a = 0
    · simp [ha]
    have hσa : σR a ≠ 0 := by simpa using ha
    rw [HeightOneSpectrum.intValuation_if_neg _ hσa, HeightOneSpectrum.intValuation_if_neg _ ha]
    congr 3
    rw [show (Ideal.span {σR a} : Ideal R) = (Ideal.span {a}).map (σR : R →+* R) by rw [Ideal.map_span, Set.image_singleton]; rfl]
    exact_mod_cast count_map σR v (by rw [Ne, Ideal.span_singleton_eq_bot]; exact ha)
  rw [key, show ((⟨σR s, hσs⟩ : R⁰) : R) = σR s from rfl, key]

end IsDedekindDomain.selmerGroup.K3aPf

end

noncomputable section

namespace NumberField
p2m_export "NumberField" "mk place RingOfIntegers RingOfIntegers.mapRingEquiv LevelArith.exists_continuousH1Sr_sUnitsMaxRep_linearMap_sClassGroupRep_injective_natural LevelArith.exists_continuousH1Sr_sUnitsMaxRep_linearMap_sClassGroupRep_injective LevelArith.exists_restrict_and_torsionBy_sClassGroupRep_linearEquiv_sClassTorsionP LevelArith.exists_placesAbove_inr_equiv_primesOver LevelArith.nonempty_repTorsionP_iso_repModP"
namespace LevelArith
p2m_export "NumberField.LevelArith" "levelField LevelGal levelFieldEquiv coe_levelFieldEquiv coe_levelFieldEquiv_symm levelGal levelGal_apply_coe modP modP_apply_mk repModP repTorsionP ringOfIntegersAut classGroupAut classGroupRep placesOverPrimes mem_placesOverPrimes_iff placesOverPrimes_finite sClassGroupRep sClassTorsionP IsNormalLevel orbitQuotientAction placesAbove placesRep sUnitsMax sUnitsMaxStable mem_sUnitsMaxStable_iff sUnitsMaxStable_le sUnitsMaxRep sUnitsMaxRep.val exists_continuousH1Sr_sUnitsMaxRep_linearMap_sClassGroupRep_injective_natural exists_continuousH1Sr_sUnitsMaxRep_linearMap_sClassGroupRep_injective exists_restrict_and_torsionBy_sClassGroupRep_linearEquiv_sClassTorsionP exists_placesAbove_inr_equiv_primesOver nonempty_repTorsionP_iso_repModP sUnitsMaxStable_eq_sUnitsMax"
namespace EQBK
p2m_open "NumberField.LevelArith NumberField~mem_placesOverPrimes_iff~placesOverPrimes"

open groupCohomology CategoryTheory
p2m_open_scoped "NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith"

variable (S : Finset Nat.Primes) (L : IntermediateField ℚ (AlgebraicClosure ℚ))

local notation "Γ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

def Normalizes (σ : Γ) : Prop := ∀ s : ↥L.fixingSubgroup, σ⁻¹ * (s : Γ) * σ ∈ L.fixingSubgroup

variable {L}

def conjHom {σ : Γ} (hσ : Normalizes L σ) : ↥L.fixingSubgroup →* ↥L.fixingSubgroup where
  toFun s := ⟨σ⁻¹ * (s : Γ) * σ, hσ s⟩
  map_one' := Subtype.ext (by simp)
  map_mul' s t := Subtype.ext (by
    change σ⁻¹ * ((s : Γ) * t) * σ = σ⁻¹ * s * σ * (σ⁻¹ * t * σ)
    group)

@[scoped simp] theorem conjHom_coe {σ : Γ} (hσ : Normalizes L σ) (s : ↥L.fixingSubgroup) : ((conjHom hσ s : ↥L.fixingSubgroup) : Γ) = σ⁻¹ * s * σ := rfl

variable (L)

def galES (σ : Γ) : sUnitsMaxRep S L →+ sUnitsMaxRep S L where
  toFun x := ⟨Additive.ofMul (σ • sUnitsMaxRep.val S L x), by
    change Additive.toMul (Additive.ofMul (σ • sUnitsMaxRep.val S L x)) ∈ sUnitsMaxStable S L
    rw [toMul_ofMul, sUnitsMaxStable_eq_sUnitsMax]
    have hx : sUnitsMaxRep.val S L x ∈ sUnitsMax S := sUnitsMaxStable_le S L x.2

    have := (sUnitsMaxStable_eq_sUnitsMax S ⊥).symm ▸ hx
    rw [mem_sUnitsMaxStable_iff] at this
    exact this ⟨σ, by simp [IntermediateField.fixingSubgroup_bot]⟩⟩
  map_zero' := Subtype.ext (by
    change Additive.ofMul (σ • sUnitsMaxRep.val S L 0) = (0 : Additive (AlgebraicClosure ℚ)ˣ)
    rw [show sUnitsMaxRep.val S L 0 = 1 from rfl, smul_one, ofMul_one])
  map_add' x y := Subtype.ext (by
    change Additive.ofMul (σ • sUnitsMaxRep.val S L (x + y)) =
      Additive.ofMul (σ • sUnitsMaxRep.val S L x) + Additive.ofMul (σ • sUnitsMaxRep.val S L y)
    rw [show sUnitsMaxRep.val S L (x + y) = sUnitsMaxRep.val S L x * sUnitsMaxRep.val S L y from rfl, smul_mul', ofMul_mul])

theorem val_galES (σ : Γ) (x : sUnitsMaxRep S L) : sUnitsMaxRep.val S L (galES S L σ x) = σ • sUnitsMaxRep.val S L x := rfl

theorem galES_ρ {σ : Γ} (s : ↥L.fixingSubgroup) (x : sUnitsMaxRep S L) (t : ↥L.fixingSubgroup) (ht : (t : Γ) = σ * s * σ⁻¹) :
    galES S L σ ((sUnitsMaxRep S L).ρ s x) = (sUnitsMaxRep S L).ρ t (galES S L σ x) := by
  apply Subtype.ext
  apply congrArg Additive.ofMul
  change σ • ((s : Γ) • sUnitsMaxRep.val S L x) = (t : Γ) • (σ • sUnitsMaxRep.val S L x)
  rw [← mul_smul, ← mul_smul, ht, inv_mul_cancel_right]

end NumberField.LevelArith.EQBK
p2m_reactivate "P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith.EQBK"
p2m_reactivate "P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith"
p2m_reactivate "P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField"

end
p2m_reactivate "P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith.EQBK"

noncomputable section

namespace NumberField
p2m_export "NumberField" "mk place RingOfIntegers RingOfIntegers.mapRingEquiv LevelArith.exists_continuousH1Sr_sUnitsMaxRep_linearMap_sClassGroupRep_injective_natural LevelArith.exists_continuousH1Sr_sUnitsMaxRep_linearMap_sClassGroupRep_injective LevelArith.exists_restrict_and_torsionBy_sClassGroupRep_linearEquiv_sClassTorsionP LevelArith.exists_placesAbove_inr_equiv_primesOver LevelArith.nonempty_repTorsionP_iso_repModP"
namespace LevelArith
p2m_export "NumberField.LevelArith" "levelField LevelGal levelFieldEquiv coe_levelFieldEquiv coe_levelFieldEquiv_symm levelGal levelGal_apply_coe modP modP_apply_mk repModP repTorsionP ringOfIntegersAut classGroupAut classGroupRep placesOverPrimes mem_placesOverPrimes_iff placesOverPrimes_finite sClassGroupRep sClassTorsionP IsNormalLevel orbitQuotientAction placesAbove placesRep sUnitsMax sUnitsMaxStable mem_sUnitsMaxStable_iff sUnitsMaxStable_le sUnitsMaxRep sUnitsMaxRep.val exists_continuousH1Sr_sUnitsMaxRep_linearMap_sClassGroupRep_injective_natural exists_continuousH1Sr_sUnitsMaxRep_linearMap_sClassGroupRep_injective exists_restrict_and_torsionBy_sClassGroupRep_linearEquiv_sClassTorsionP exists_placesAbove_inr_equiv_primesOver nonempty_repTorsionP_iso_repModP sUnitsMaxStable_eq_sUnitsMax"
namespace EQBK
p2m_open "NumberField.LevelArith NumberField~mem_placesOverPrimes_iff~placesOverPrimes"

open groupCohomology CategoryTheory
p2m_open_scoped "NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith"

variable (S : Finset Nat.Primes) {L : IntermediateField ℚ (AlgebraicClosure ℚ)}

local notation "Γ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

def conjCocycle₁ {σ : Γ} (hσ : Normalizes L σ) (c : cocycles₁ (sUnitsMaxRep S L)) : cocycles₁ (sUnitsMaxRep S L) :=
  ⟨fun s => galES S L σ (c (conjHom hσ s)), by
    rw [mem_cocycles₁_iff]
    intro s t
    have hc := (mem_cocycles₁_iff (A := sUnitsMaxRep S L) c).1 c.2 (conjHom hσ s) (conjHom hσ t)
    rw [← map_mul] at hc
    change galES S L σ (c (conjHom hσ (s * t))) = (sUnitsMaxRep S L).ρ s (galES S L σ (c (conjHom hσ t))) + galES S L σ (c (conjHom hσ s))
    rw [hc, map_add, galES_ρ S L (conjHom hσ s) _ s (by rw [conjHom_coe]; group)]⟩

@[scoped simp] theorem conjCocycle₁_apply {σ : Γ} (hσ : Normalizes L σ) (c : cocycles₁ (sUnitsMaxRep S L)) (s : ↥L.fixingSubgroup) :
    conjCocycle₁ S hσ c s = galES S L σ (c (conjHom hσ s)) := rfl

theorem conjCocycle₁_add {σ : Γ} (hσ : Normalizes L σ) (c c' : cocycles₁ (sUnitsMaxRep S L)) :
    conjCocycle₁ S hσ (c + c') = conjCocycle₁ S hσ c + conjCocycle₁ S hσ c' := by
  apply Subtype.ext; funext s
  exact map_add (galES S L σ) (c (conjHom hσ s)) (c' (conjHom hσ s))

theorem isLevelConstantSr₁_conjCocycle₁ {σ : Γ} (hσ : Normalizes L σ) {c : cocycles₁ (sUnitsMaxRep S L)}
    (hc : IsLevelConstantSr₁ L.fixingSubgroup.subtype S c) : IsLevelConstantSr₁ L.fixingSubgroup.subtype S (conjCocycle₁ S hσ c) := by
  obtain ⟨F, hF, h⟩ := hc
  refine ⟨F.map (σ : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ), hF.map_algEquiv σ, fun g s hs => ?_⟩
  change galES S L σ (c (conjHom hσ (g * s))) = galES S L σ (c (conjHom hσ g))
  rw [map_mul]
  refine congrArg (galES S L σ) (h _ _ ?_)

  rw [Subgroup.coe_subtype, conjHom_coe, IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  have hs' := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hs (σ x) ⟨x, hx, rfl⟩
  change (σ⁻¹ * (s : Γ) * σ) x = x
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply]
  change σ⁻¹ ((L.fixingSubgroup.subtype s) (σ x)) = x
  rw [hs']
  exact σ.symm_apply_apply x

end NumberField.LevelArith.EQBK
p2m_reactivate "P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith.EQBK"
p2m_reactivate "P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith.EQBK"
p2m_reactivate "P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith.EQBK"

end
p2m_reactivate "P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith.EQBK"

noncomputable section

namespace NumberField
p2m_export "NumberField" "mk place RingOfIntegers RingOfIntegers.mapRingEquiv LevelArith.exists_continuousH1Sr_sUnitsMaxRep_linearMap_sClassGroupRep_injective_natural LevelArith.exists_continuousH1Sr_sUnitsMaxRep_linearMap_sClassGroupRep_injective LevelArith.exists_restrict_and_torsionBy_sClassGroupRep_linearEquiv_sClassTorsionP LevelArith.exists_placesAbove_inr_equiv_primesOver LevelArith.nonempty_repTorsionP_iso_repModP"
namespace LevelArith
p2m_export "NumberField.LevelArith" "levelField LevelGal levelFieldEquiv coe_levelFieldEquiv coe_levelFieldEquiv_symm levelGal levelGal_apply_coe modP modP_apply_mk repModP repTorsionP ringOfIntegersAut classGroupAut classGroupRep placesOverPrimes mem_placesOverPrimes_iff placesOverPrimes_finite sClassGroupRep sClassTorsionP IsNormalLevel orbitQuotientAction placesAbove placesRep sUnitsMax sUnitsMaxStable mem_sUnitsMaxStable_iff sUnitsMaxStable_le sUnitsMaxRep sUnitsMaxRep.val exists_continuousH1Sr_sUnitsMaxRep_linearMap_sClassGroupRep_injective_natural exists_continuousH1Sr_sUnitsMaxRep_linearMap_sClassGroupRep_injective exists_restrict_and_torsionBy_sClassGroupRep_linearEquiv_sClassTorsionP exists_placesAbove_inr_equiv_primesOver nonempty_repTorsionP_iso_repModP sUnitsMaxStable_eq_sUnitsMax"
namespace EQBK
p2m_open "NumberField.LevelArith NumberField~mem_placesOverPrimes_iff~placesOverPrimes"

open groupCohomology CategoryTheory
p2m_open_scoped "NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith Pointwise"

variable (S : Finset Nat.Primes) {L : IntermediateField ℚ (AlgebraicClosure ℚ)}

local notation "Γ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

theorem H1π_conjCocycle₁_congr {σ : Γ} (hσ : Normalizes L σ) {c c' : cocycles₁ (sUnitsMaxRep S L)}
    (h : (H1π (sUnitsMaxRep S L)).hom c = (H1π (sUnitsMaxRep S L)).hom c') :
    (H1π (sUnitsMaxRep S L)).hom (conjCocycle₁ S hσ c) = (H1π (sUnitsMaxRep S L)).hom (conjCocycle₁ S hσ c') := by
  rw [H1π_eq_iff] at h ⊢
  obtain ⟨a, ha⟩ := h
  refine ⟨galES S L σ a, ?_⟩
  funext s
  have hs := congrFun ha (conjHom hσ s)
  change (d₀₁ (sUnitsMaxRep S L)).hom a (conjHom hσ s) = c (conjHom hσ s) - c' (conjHom hσ s) at hs
  change (d₀₁ (sUnitsMaxRep S L)).hom (galES S L σ a) s = galES S L σ (c (conjHom hσ s)) - galES S L σ (c' (conjHom hσ s))
  rw [← map_sub, ← hs, d₀₁_hom_apply, d₀₁_hom_apply, map_sub, galES_ρ S L (conjHom hσ s) a s (by rw [conjHom_coe]; group)]

theorem H1π_conjCocycle₁_of_mem {σ : Γ} (hσL : σ ∈ L.fixingSubgroup) (c : cocycles₁ (sUnitsMaxRep S L)) :
    (H1π (sUnitsMaxRep S L)).hom (conjCocycle₁ S (fun s => Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hσL) s.2) hσL) c) =
      (H1π (sUnitsMaxRep S L)).hom c := by
  rw [H1π_eq_iff]
  refine ⟨c ⟨σ, hσL⟩, ?_⟩
  funext s
  have hσ : Normalizes L σ := fun s => Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hσL) s.2) hσL

  have h1 := (mem_cocycles₁_iff (A := sUnitsMaxRep S L) c).1 c.2
  let σ' : ↥L.fixingSubgroup := ⟨σ, hσL⟩
  let E := sUnitsMaxRep S L
  have hρρ : ∀ y : E, E.ρ σ' (E.ρ σ'⁻¹ y) = y := fun y => by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have hC : c σ'⁻¹ = -(E.ρ σ'⁻¹ (c σ')) := by
    have := h1 σ'⁻¹ σ'
    rw [inv_mul_cancel, cocycles₁_map_one] at this
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact this.symm
  have hB : c (s * σ') = E.ρ s (c σ') + c s := h1 s σ'
  have hconj : conjHom hσ s = σ'⁻¹ * (s * σ') := Subtype.ext (by rw [conjHom_coe, mul_assoc]; rfl)
  have hA : c (conjHom hσ s) = E.ρ σ'⁻¹ (c (s * σ')) + c σ'⁻¹ := by rw [hconj]; exact h1 _ _
  have hG : ∀ x : E, galES S L σ x = E.ρ σ' x := fun x => rfl
  change (d₀₁ E).hom (c σ') s = galES S L σ (c (conjHom hσ s)) - c s
  rw [d₀₁_hom_apply, hG, hA, map_add, hρρ, hB, hC, map_neg, hρρ]
  abel

end NumberField.LevelArith.EQBK
p2m_reactivate "P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith.EQBK"
p2m_reactivate "P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith.EQBK"
p2m_reactivate "P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith.EQBK"

end
p2m_reactivate "P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith.EQBK"

noncomputable section

namespace NumberField
p2m_export "NumberField" "mk place RingOfIntegers RingOfIntegers.mapRingEquiv LevelArith.exists_continuousH1Sr_sUnitsMaxRep_linearMap_sClassGroupRep_injective_natural LevelArith.exists_continuousH1Sr_sUnitsMaxRep_linearMap_sClassGroupRep_injective LevelArith.exists_restrict_and_torsionBy_sClassGroupRep_linearEquiv_sClassTorsionP LevelArith.exists_placesAbove_inr_equiv_primesOver LevelArith.nonempty_repTorsionP_iso_repModP"
namespace LevelArith
p2m_export "NumberField.LevelArith" "levelField LevelGal levelFieldEquiv coe_levelFieldEquiv coe_levelFieldEquiv_symm levelGal levelGal_apply_coe modP modP_apply_mk repModP repTorsionP ringOfIntegersAut classGroupAut classGroupRep placesOverPrimes mem_placesOverPrimes_iff placesOverPrimes_finite sClassGroupRep sClassTorsionP IsNormalLevel orbitQuotientAction placesAbove placesRep sUnitsMax sUnitsMaxStable mem_sUnitsMaxStable_iff sUnitsMaxStable_le sUnitsMaxRep sUnitsMaxRep.val exists_continuousH1Sr_sUnitsMaxRep_linearMap_sClassGroupRep_injective_natural exists_continuousH1Sr_sUnitsMaxRep_linearMap_sClassGroupRep_injective exists_restrict_and_torsionBy_sClassGroupRep_linearEquiv_sClassTorsionP exists_placesAbove_inr_equiv_primesOver nonempty_repTorsionP_iso_repModP sUnitsMaxStable_eq_sUnitsMax"
namespace EQBK
p2m_open "NumberField.LevelArith NumberField~mem_placesOverPrimes_iff~placesOverPrimes"

open groupCohomology CategoryTheory
p2m_open_scoped "NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith Pointwise"

variable (S : Finset Nat.Primes) (K L : IntermediateField ℚ (AlgebraicClosure ℚ))
  (hnorm : ∀ g ∈ K.fixingSubgroup, ∀ s ∈ L.fixingSubgroup, g * s * g⁻¹ ∈ L.fixingSubgroup)

local notation "Γ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

include hnorm in
theorem normalizes_of_mem (γ : ↥K.fixingSubgroup) : Normalizes L (γ : Γ) := fun s => by
  have := hnorm (γ : Γ)⁻¹ (Subgroup.inv_mem _ γ.2) s s.2
  rwa [inv_inv] at this

abbrev X : Submodule ℤ (H1 (sUnitsMaxRep S L)) := continuousH1Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L)

def repr (x : ↥(X S L)) : cocycles₁ (sUnitsMaxRep S L) := Classical.choose ((mem_continuousH1Sr_iff _ S _ x.1).1 x.2)

theorem repr_spec (x : ↥(X S L)) : IsLevelConstantSr₁ L.fixingSubgroup.subtype S (repr S L x) ∧ (H1π _).hom (repr S L x) = x.1 :=
  Classical.choose_spec ((mem_continuousH1Sr_iff _ S _ x.1).1 x.2)

def conjXFun (γ : ↥K.fixingSubgroup) (x : ↥(X S L)) : ↥(X S L) :=
  ⟨(H1π _).hom (conjCocycle₁ S (normalizes_of_mem K L hnorm γ) (repr S L x)),
    H1π_mem_continuousH1Sr _ S _ (isLevelConstantSr₁_conjCocycle₁ S _ (repr_spec S L x).1)⟩

theorem conjXFun_mk (γ : ↥K.fixingSubgroup) (c : cocycles₁ (sUnitsMaxRep S L)) (hc : IsLevelConstantSr₁ L.fixingSubgroup.subtype S c) :
    (conjXFun S K L hnorm γ ⟨(H1π _).hom c, H1π_mem_continuousH1Sr _ S _ hc⟩ : ↥(X S L)).1 =
      (H1π _).hom (conjCocycle₁ S (normalizes_of_mem K L hnorm γ) c) :=
  H1π_conjCocycle₁_congr S _ (repr_spec S L ⟨(H1π _).hom c, H1π_mem_continuousH1Sr _ S _ hc⟩).2

theorem X_induction {P : ↥(X S L) → Prop}
    (h : ∀ (c : cocycles₁ (sUnitsMaxRep S L)) (hc : IsLevelConstantSr₁ L.fixingSubgroup.subtype S c), P ⟨(H1π _).hom c, H1π_mem_continuousH1Sr _ S _ hc⟩)
    (x : ↥(X S L)) : P x := by
  obtain ⟨hc, hx⟩ := repr_spec S L x
  have : x = ⟨(H1π _).hom (repr S L x), H1π_mem_continuousH1Sr _ S _ hc⟩ := Subtype.ext hx.symm
  rw [this]; exact h _ hc

def conjX (γ : ↥K.fixingSubgroup) : ↥(X S L) →+ ↥(X S L) where
  toFun := conjXFun S K L hnorm γ
  map_zero' := by
    apply Subtype.ext
    have h := conjXFun_mk S K L hnorm γ 0 (isLevelConstantSr₁_const _ S _)
    have h0 : (⟨(H1π _).hom (0 : cocycles₁ (sUnitsMaxRep S L)), H1π_mem_continuousH1Sr _ S _ (isLevelConstantSr₁_const _ S _)⟩ : ↥(X S L)) = 0 :=
      Subtype.ext (map_zero _)
    rw [h0] at h
    rw [h, show conjCocycle₁ S (normalizes_of_mem K L hnorm γ) 0 = 0 from Subtype.ext (funext fun s => map_zero (galES S L _)), map_zero]
    rfl
  map_add' x y := by
    induction x using X_induction S L with
    | h c hc =>
    induction y using X_induction S L with
    | h c' hc' =>
    apply Subtype.ext
    have hsum : (⟨(H1π _).hom c, H1π_mem_continuousH1Sr _ S _ hc⟩ + ⟨(H1π _).hom c', H1π_mem_continuousH1Sr _ S _ hc'⟩ : ↥(X S L)) =
        ⟨(H1π _).hom (c + c'), H1π_mem_continuousH1Sr _ S _ (hc.add hc')⟩ := Subtype.ext (map_add _ _ _).symm
    rw [hsum, conjXFun_mk (hc := hc.add hc'), conjCocycle₁_add, map_add]
    change _ = ((conjXFun S K L hnorm γ _ : ↥(X S L)).1 + (conjXFun S K L hnorm γ _ : ↥(X S L)).1)
    rw [conjXFun_mk (hc := hc), conjXFun_mk (hc := hc')]

theorem conjX_mk (γ : ↥K.fixingSubgroup) (c : cocycles₁ (sUnitsMaxRep S L)) (hc : IsLevelConstantSr₁ L.fixingSubgroup.subtype S c) :
    (conjX S K L hnorm γ ⟨(H1π _).hom c, H1π_mem_continuousH1Sr _ S _ hc⟩ : ↥(X S L)).1 =
      (H1π _).hom (conjCocycle₁ S (normalizes_of_mem K L hnorm γ) c) := conjXFun_mk S K L hnorm γ c hc

end NumberField.LevelArith.EQBK
p2m_reactivate "P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith.EQBK"
p2m_reactivate "P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith.EQBK"
p2m_reactivate "P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith.EQBK"

end
p2m_reactivate "P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith.EQBK"

noncomputable section

namespace NumberField
p2m_export "NumberField" "mk place RingOfIntegers RingOfIntegers.mapRingEquiv LevelArith.exists_continuousH1Sr_sUnitsMaxRep_linearMap_sClassGroupRep_injective_natural LevelArith.exists_continuousH1Sr_sUnitsMaxRep_linearMap_sClassGroupRep_injective LevelArith.exists_restrict_and_torsionBy_sClassGroupRep_linearEquiv_sClassTorsionP LevelArith.exists_placesAbove_inr_equiv_primesOver LevelArith.nonempty_repTorsionP_iso_repModP"
namespace LevelArith
p2m_export "NumberField.LevelArith" "levelField LevelGal levelFieldEquiv coe_levelFieldEquiv coe_levelFieldEquiv_symm levelGal levelGal_apply_coe modP modP_apply_mk repModP repTorsionP ringOfIntegersAut classGroupAut classGroupRep placesOverPrimes mem_placesOverPrimes_iff placesOverPrimes_finite sClassGroupRep sClassTorsionP IsNormalLevel orbitQuotientAction placesAbove placesRep sUnitsMax sUnitsMaxStable mem_sUnitsMaxStable_iff sUnitsMaxStable_le sUnitsMaxRep sUnitsMaxRep.val exists_continuousH1Sr_sUnitsMaxRep_linearMap_sClassGroupRep_injective_natural exists_continuousH1Sr_sUnitsMaxRep_linearMap_sClassGroupRep_injective exists_restrict_and_torsionBy_sClassGroupRep_linearEquiv_sClassTorsionP exists_placesAbove_inr_equiv_primesOver nonempty_repTorsionP_iso_repModP sUnitsMaxStable_eq_sUnitsMax"
namespace EQBK
p2m_open "NumberField.LevelArith NumberField~mem_placesOverPrimes_iff~placesOverPrimes"

open groupCohomology CategoryTheory
p2m_open_scoped "NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith Pointwise"

variable (S : Finset Nat.Primes) (K L : IntermediateField ℚ (AlgebraicClosure ℚ))
  (hnorm : ∀ g ∈ K.fixingSubgroup, ∀ s ∈ L.fixingSubgroup, g * s * g⁻¹ ∈ L.fixingSubgroup)

local notation "Γ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

theorem conjCocycle₁_one_eq {hσ : Normalizes L (1 : Γ)} (c : cocycles₁ (sUnitsMaxRep S L)) : conjCocycle₁ S hσ c = c := by
  apply Subtype.ext; funext s
  change galES S L 1 (c (conjHom hσ s)) = c s
  have : conjHom hσ s = s := Subtype.ext (by rw [conjHom_coe]; simp)
  rw [this]
  exact Subtype.ext (congrArg Additive.ofMul (one_smul Γ (sUnitsMaxRep.val S L (c s))))

theorem conjCocycle₁_mul_eq {σ τ : Γ} (hσ : Normalizes L σ) (hτ : Normalizes L τ) (hστ : Normalizes L (σ * τ)) (c : cocycles₁ (sUnitsMaxRep S L)) :
    conjCocycle₁ S hστ c = conjCocycle₁ S hσ (conjCocycle₁ S hτ c) := by
  apply Subtype.ext; funext s
  change galES S L (σ * τ) (c (conjHom hστ s)) = galES S L σ (galES S L τ (c (conjHom hτ (conjHom hσ s))))
  have : conjHom hστ s = conjHom hτ (conjHom hσ s) := Subtype.ext (by simp only [conjHom_coe, mul_inv_rev]; group)
  rw [this]
  exact Subtype.ext (congrArg Additive.ofMul (mul_smul σ τ (sUnitsMaxRep.val S L _)))

def XRep : Rep ℤ ↥K.fixingSubgroup :=
  Rep.of (X := ↥(X S L))
    { toFun := fun γ => { toFun := conjX S K L hnorm γ, map_add' := map_add _, map_smul' := fun n x => map_zsmul (conjX S K L hnorm γ) n x }
      map_one' := by
        apply LinearMap.ext; intro x
        induction x using X_induction S L with
        | h c hc =>
        apply Subtype.ext
        change (conjX S K L hnorm 1 _ : ↥(X S L)).1 = (H1π _).hom c
        rw [conjX_mk (hc := hc), conjCocycle₁_one_eq]
      map_mul' := fun γ δ => by
        apply LinearMap.ext; intro x
        induction x using X_induction S L with
        | h c hc =>
        apply Subtype.ext
        change (conjX S K L hnorm (γ * δ) _ : ↥(X S L)).1 = (conjX S K L hnorm γ (conjX S K L hnorm δ _) : ↥(X S L)).1
        rw [conjX_mk (hc := hc)]
        have h2 : (conjX S K L hnorm δ ⟨(H1π _).hom c, H1π_mem_continuousH1Sr _ S _ hc⟩ : ↥(X S L)) =
            ⟨(H1π _).hom (conjCocycle₁ S (normalizes_of_mem K L hnorm δ) c),
              H1π_mem_continuousH1Sr _ S _ (isLevelConstantSr₁_conjCocycle₁ S _ hc)⟩ := Subtype.ext (conjX_mk S K L hnorm δ c hc)
        rw [h2, conjX_mk (hc := isLevelConstantSr₁_conjCocycle₁ S _ hc)]
        exact congrArg _ (conjCocycle₁_mul_eq S (L := L) _ _ _ c) }

theorem XRep_ρ_apply (γ : ↥K.fixingSubgroup) (x : XRep S K L hnorm) : (XRep S K L hnorm).ρ γ x = conjX S K L hnorm γ x := rfl

theorem XRep_ρ_eq_one_of_mem (γ : ↥K.fixingSubgroup) (hγ : (γ : Γ) ∈ L.fixingSubgroup) : (XRep S K L hnorm).ρ γ = 1 := by
  apply LinearMap.ext; intro x
  induction x using X_induction S L with
  | h c hc =>
  apply Subtype.ext
  change (conjX S K L hnorm γ _ : ↥(X S L)).1 = (H1π _).hom c
  rw [conjX_mk (hc := hc)]
  exact H1π_conjCocycle₁_of_mem S hγ c

end NumberField.LevelArith.EQBK
p2m_reactivate "P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith.EQBK"
p2m_reactivate "P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith.EQBK"
p2m_reactivate "P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith.EQBK"

end
p2m_reactivate "P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith.EQBK"

noncomputable section

namespace NumberField
p2m_export "NumberField" "mk place RingOfIntegers RingOfIntegers.mapRingEquiv LevelArith.exists_continuousH1Sr_sUnitsMaxRep_linearMap_sClassGroupRep_injective_natural LevelArith.exists_continuousH1Sr_sUnitsMaxRep_linearMap_sClassGroupRep_injective LevelArith.exists_restrict_and_torsionBy_sClassGroupRep_linearEquiv_sClassTorsionP LevelArith.exists_placesAbove_inr_equiv_primesOver LevelArith.nonempty_repTorsionP_iso_repModP"
namespace LevelArith
p2m_export "NumberField.LevelArith" "levelField LevelGal levelFieldEquiv coe_levelFieldEquiv coe_levelFieldEquiv_symm levelGal levelGal_apply_coe modP modP_apply_mk repModP repTorsionP ringOfIntegersAut classGroupAut classGroupRep placesOverPrimes mem_placesOverPrimes_iff placesOverPrimes_finite sClassGroupRep sClassTorsionP IsNormalLevel orbitQuotientAction placesAbove placesRep sUnitsMax sUnitsMaxStable mem_sUnitsMaxStable_iff sUnitsMaxStable_le sUnitsMaxRep sUnitsMaxRep.val exists_continuousH1Sr_sUnitsMaxRep_linearMap_sClassGroupRep_injective_natural exists_continuousH1Sr_sUnitsMaxRep_linearMap_sClassGroupRep_injective exists_restrict_and_torsionBy_sClassGroupRep_linearEquiv_sClassTorsionP exists_placesAbove_inr_equiv_primesOver nonempty_repTorsionP_iso_repModP sUnitsMaxStable_eq_sUnitsMax"
namespace EQBK
p2m_open "NumberField.LevelArith NumberField~mem_placesOverPrimes_iff~placesOverPrimes"

p2m_open "groupCohomology CategoryTheory IsDedekindDomain P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.IsDedekindDomain"
p2m_open_scoped "NumberField P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith Pointwise"

variable (S : Finset Nat.Primes) (K L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hKL : K ≤ L)
  [FiniteDimensional ℚ ↥K] [FiniteDimensional ℚ ↥L] [Normal ↥K ↥(levelField K L hKL)]

local notation "Γ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

def τ (γ : ↥K.fixingSubgroup) : ↥L ≃ₐ[ℚ] ↥L :=
  AlgEquiv.ofRingEquiv (f := (levelFieldEquiv K L hKL).trans (((levelGal K L hKL γ : LevelGal K L hKL) : ↥(levelField K L hKL) ≃+* ↥(levelField K L hKL)).trans
    (levelFieldEquiv K L hKL).symm)) fun q => by simp

@[scoped simp] theorem coe_τ (γ : ↥K.fixingSubgroup) (y : ↥L) : ((τ K L hKL γ y : ↥L) : AlgebraicClosure ℚ) = (γ : Γ) (y : AlgebraicClosure ℚ) := by
  change ((((levelFieldEquiv K L hKL).symm) (levelGal K L hKL γ (levelFieldEquiv K L hKL y)) : ↥L) : AlgebraicClosure ℚ) = _
  rw [coe_levelFieldEquiv_symm, levelGal_apply_coe, coe_levelFieldEquiv]

theorem τ_mul (γ δ : ↥K.fixingSubgroup) : τ K L hKL (γ * δ) = τ K L hKL γ * τ K L hKL δ :=
  AlgEquiv.ext fun y => Subtype.ext (by rw [AlgEquiv.mul_apply, coe_τ, coe_τ, coe_τ]; rfl)

theorem τ_one : τ K L hKL 1 = 1 := AlgEquiv.ext fun y => Subtype.ext (by rw [coe_τ]; rfl)

def τHom : ↥K.fixingSubgroup →* (↥L ≃ₐ[ℚ] ↥L) where
  toFun := τ K L hKL
  map_one' := τ_one K L hKL
  map_mul' := τ_mul K L hKL

theorem τ_eq_one_of_mem (γ : ↥K.fixingSubgroup) (hγ : (γ : Γ) ∈ L.fixingSubgroup) : τ K L hKL γ = 1 :=
  AlgEquiv.ext fun y => Subtype.ext (by rw [coe_τ]; exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hγ _ y.2)

def comapPrime (σ : 𝓞 ↥L ≃+* 𝓞 ↥L) (w : HeightOneSpectrum (𝓞 ↥L)) : HeightOneSpectrum (𝓞 ↥L) where
  asIdeal := w.asIdeal.comap (σ : 𝓞 ↥L →+* 𝓞 ↥L)
  isPrime := Ideal.comap_isPrime _ _
  ne_bot h := by
    have e : Ideal.map (σ : 𝓞 ↥L →+* 𝓞 ↥L) (w.asIdeal.comap (σ : 𝓞 ↥L →+* 𝓞 ↥L)) = w.asIdeal := Ideal.map_comap_of_surjective _ σ.surjective _
    rw [h, Ideal.map_bot] at e
    exact w.ne_bot e.symm

theorem comapPrime_mem (σ : 𝓞 ↥L ≃+* 𝓞 ↥L) {w : HeightOneSpectrum (𝓞 ↥L)} (hw : w ∈ placesOverPrimes ↥L (S : Set Nat.Primes)) :
    comapPrime L σ w ∈ placesOverPrimes ↥L (S : Set Nat.Primes) := by
  rw [mem_placesOverPrimes_iff] at hw ⊢
  obtain ⟨q, hq, hqw⟩ := hw
  exact ⟨q, hq, by change σ _ ∈ w.asIdeal; rwa [map_natCast]⟩

theorem comapPrime_refl (w : HeightOneSpectrum (𝓞 ↥L)) : comapPrime L (RingEquiv.refl _) w = w :=
  HeightOneSpectrum.ext (by change w.asIdeal.comap (RingHom.id _) = w.asIdeal; exact Ideal.comap_id _)

theorem comapPrime_trans (σ₁ σ₂ : 𝓞 ↥L ≃+* 𝓞 ↥L) (w : HeightOneSpectrum (𝓞 ↥L)) :
    comapPrime L (σ₁.trans σ₂) w = comapPrime L σ₁ (comapPrime L σ₂ w) :=
  HeightOneSpectrum.ext (by
    change w.asIdeal.comap ((σ₂ : 𝓞 ↥L →+* 𝓞 ↥L).comp (σ₁ : 𝓞 ↥L →+* 𝓞 ↥L)) = (w.asIdeal.comap (σ₂ : 𝓞 ↥L →+* 𝓞 ↥L)).comap (σ₁ : 𝓞 ↥L →+* 𝓞 ↥L)
    exact (Ideal.comap_comap _ _).symm)

def placePull (γ : ↥K.fixingSubgroup) (w : ↥(placesOverPrimes ↥L (S : Set Nat.Primes))) : ↥(placesOverPrimes ↥L (S : Set Nat.Primes)) :=
  ⟨comapPrime L (ringOfIntegersAut ℚ ↥L (τ K L hKL γ)) w.1, comapPrime_mem S L _ w.2⟩

theorem placePull_one (w : ↥(placesOverPrimes ↥L (S : Set Nat.Primes))) : placePull S K L hKL 1 w = w := by
  apply Subtype.ext
  change comapPrime L (ringOfIntegersAut ℚ ↥L (τ K L hKL 1)) w.1 = w.1
  rw [τ_one, show ringOfIntegersAut ℚ ↥L (1 : ↥L ≃ₐ[ℚ] ↥L) = RingEquiv.refl _ from RingEquiv.ext fun _ => rfl, comapPrime_refl]

theorem placePull_mul (γ δ : ↥K.fixingSubgroup) (w : ↥(placesOverPrimes ↥L (S : Set Nat.Primes))) :
    placePull S K L hKL (γ * δ) w = placePull S K L hKL δ (placePull S K L hKL γ w) := by
  apply Subtype.ext
  change comapPrime L (ringOfIntegersAut ℚ ↥L (τ K L hKL (γ * δ))) w.1 =
    comapPrime L (ringOfIntegersAut ℚ ↥L (τ K L hKL δ)) (comapPrime L (ringOfIntegersAut ℚ ↥L (τ K L hKL γ)) w.1)
  rw [τ_mul, show ringOfIntegersAut ℚ ↥L (τ K L hKL γ * τ K L hKL δ) =
    (ringOfIntegersAut ℚ ↥L (τ K L hKL δ)).trans (ringOfIntegersAut ℚ ↥L (τ K L hKL γ)) from RingEquiv.ext fun _ => rfl, comapPrime_trans]

variable (p : ℕ)

def PlRep : Rep (ZMod p) ↥K.fixingSubgroup :=
  Rep.of (X := ↥(placesOverPrimes ↥L (S : Set Nat.Primes)) → ZMod p)
    { toFun := fun γ => LinearMap.funLeft (ZMod p) (ZMod p) (placePull S K L hKL γ)
      map_one' := by apply LinearMap.ext; intro f; funext w; change f (placePull S K L hKL 1 w) = f w; rw [placePull_one]
      map_mul' := fun γ δ => by
        apply LinearMap.ext; intro f; funext w
        change f (placePull S K L hKL (γ * δ) w) = f (placePull S K L hKL δ (placePull S K L hKL γ w))
        rw [placePull_mul] }

theorem PlRep_ρ_apply (γ : ↥K.fixingSubgroup) (f : PlRep S K L hKL p) (w : ↥(placesOverPrimes ↥L (S : Set Nat.Primes))) :
    (PlRep S K L hKL p).ρ γ f w = f (placePull S K L hKL γ w) := rfl

theorem PlRep_ρ_eq_one_of_mem (γ : ↥K.fixingSubgroup) (hγ : (γ : Γ) ∈ L.fixingSubgroup) : (PlRep S K L hKL p).ρ γ = 1 := by
  apply LinearMap.ext; intro f; funext w
  change f (placePull S K L hKL γ w) = f w
  congr 1
  apply Subtype.ext
  change comapPrime L (ringOfIntegersAut ℚ ↥L (τ K L hKL γ)) w.1 = w.1
  rw [τ_eq_one_of_mem K L hKL γ hγ, show ringOfIntegersAut ℚ ↥L (1 : ↥L ≃ₐ[ℚ] ↥L) = RingEquiv.refl _ from RingEquiv.ext fun _ => rfl, comapPrime_refl]

end NumberField.LevelArith.EQBK
p2m_reactivate "P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith.EQBK"
p2m_reactivate "P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith.EQBK"
p2m_reactivate "P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith.EQBK"

end
p2m_reactivate "P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith.EQBK"

noncomputable section

namespace NumberField
p2m_export "NumberField" "mk place RingOfIntegers RingOfIntegers.mapRingEquiv LevelArith.exists_continuousH1Sr_sUnitsMaxRep_linearMap_sClassGroupRep_injective_natural LevelArith.exists_continuousH1Sr_sUnitsMaxRep_linearMap_sClassGroupRep_injective LevelArith.exists_restrict_and_torsionBy_sClassGroupRep_linearEquiv_sClassTorsionP LevelArith.exists_placesAbove_inr_equiv_primesOver LevelArith.nonempty_repTorsionP_iso_repModP"
namespace LevelArith
p2m_export "NumberField.LevelArith" "levelField LevelGal levelFieldEquiv coe_levelFieldEquiv coe_levelFieldEquiv_symm levelGal levelGal_apply_coe modP modP_apply_mk repModP repTorsionP ringOfIntegersAut classGroupAut classGroupRep placesOverPrimes mem_placesOverPrimes_iff placesOverPrimes_finite sClassGroupRep sClassTorsionP IsNormalLevel orbitQuotientAction placesAbove placesRep sUnitsMax sUnitsMaxStable mem_sUnitsMaxStable_iff sUnitsMaxStable_le sUnitsMaxRep sUnitsMaxRep.val exists_continuousH1Sr_sUnitsMaxRep_linearMap_sClassGroupRep_injective_natural exists_continuousH1Sr_sUnitsMaxRep_linearMap_sClassGroupRep_injective exists_restrict_and_torsionBy_sClassGroupRep_linearEquiv_sClassTorsionP exists_placesAbove_inr_equiv_primesOver nonempty_repTorsionP_iso_repModP sUnitsMaxStable_eq_sUnitsMax"
namespace EQBK
p2m_open "NumberField.LevelArith NumberField~mem_placesOverPrimes_iff~placesOverPrimes"

p2m_open "groupCohomology CategoryTheory IsDedekindDomain P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.IsDedekindDomain ExtCitation"
p2m_open_scoped "NumberField P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith Pointwise"

variable (S : Finset Nat.Primes) (K L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hKL : K ≤ L) (hL : L.IsUnramifiedOutside S) (p : ℕ) [Fact p.Prime]
  [(L.fixingSubgroup.subgroupOf K.fixingSubgroup).Normal] [(L.fixingSubgroup.subgroupOf K.fixingSubgroup).FiniteIndex]

local notation "Γ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

abbrev μ : Rep (ZMod p) ↥L.fixingSubgroup := (Rep.trivial (ZMod p) ↥L.fixingSubgroup (ZMod p)).twist ((cycloChar p).comp L.fixingSubgroup.subtype)

abbrev V₂ : Type := continuousH2Sr L.fixingSubgroup.subtype S (μ L p)

def Θ : continuousH2Sr K.fixingSubgroup.subtype S (cyclotomicQuotientRep K L p) ≃ₗ[ZMod p] V₂ S L p :=
  Classical.choose (groupCohomology.exists_continuousH2Sr_cyclotomicQuotientRep_equiv_pin S K L hKL hL (p := p))

def Block₂ (σ : Γ) (w w' : ↥(levelCocyclesSr₂ L.fixingSubgroup.subtype S (μ L p))) : Prop :=
  ∀ s t s' t' : ↥L.fixingSubgroup, σ⁻¹ * (s : Γ) * σ = s' → σ⁻¹ * (t : Γ) * σ = t' →
    (w' : ↥L.fixingSubgroup × ↥L.fixingSubgroup → ZMod p) (s, t) =
      ((cycloChar p σ : (ZMod p)ˣ) : ZMod p) * (w : ↥L.fixingSubgroup × ↥L.fixingSubgroup → ZMod p) (s', t')

theorem Θ_equiv (γ : ↥K.fixingSubgroup) (a : continuousH2Sr K.fixingSubgroup.subtype S (cyclotomicQuotientRep K L p))
    (w w' : ↥(levelCocyclesSr₂ L.fixingSubgroup.subtype S (μ L p)))
    (ha : Θ S K L hKL hL p a = continuousH2Srπ L.fixingSubgroup.subtype S _ w) (hb : Block₂ S L p (γ : Γ) w w') :
    Θ S K L hKL hL p ((cyclotomicQuotientH2Rep S K L p).ρ γ a) = continuousH2Srπ L.fixingSubgroup.subtype S _ w' := by
  rw [cyclotomicQuotientH2Rep_ρ_apply]
  exact (Classical.choose_spec (groupCohomology.exists_continuousH2Sr_cyclotomicQuotientRep_equiv_pin S K L hKL hL (p := p))).2 γ a w w' ha hb

attribute [irreducible] Θ

def H2ρ : Representation (ZMod p) ↥K.fixingSubgroup (V₂ S L p) where
  toFun γ := (Θ S K L hKL hL p).toLinearMap ∘ₗ (cyclotomicQuotientH2Rep S K L p).ρ γ ∘ₗ (Θ S K L hKL hL p).symm.toLinearMap
  map_one' := LinearMap.ext fun v => by
    change Θ S K L hKL hL p ((cyclotomicQuotientH2Rep S K L p).ρ 1 ((Θ S K L hKL hL p).symm v)) = v
    have h1 := LinearMap.congr_fun (cyclotomicQuotientH2Rep S K L p).ρ.map_one ((Θ S K L hKL hL p).symm v)
    exact (congrArg (Θ S K L hKL hL p) h1).trans ((Θ S K L hKL hL p).apply_symm_apply v)
  map_mul' γ δ := LinearMap.ext fun v => by
    change Θ S K L hKL hL p ((cyclotomicQuotientH2Rep S K L p).ρ (γ * δ) ((Θ S K L hKL hL p).symm v)) =
      Θ S K L hKL hL p ((cyclotomicQuotientH2Rep S K L p).ρ γ ((Θ S K L hKL hL p).symm
        (Θ S K L hKL hL p ((cyclotomicQuotientH2Rep S K L p).ρ δ ((Θ S K L hKL hL p).symm v)))))
    have h := LinearMap.congr_fun ((cyclotomicQuotientH2Rep S K L p).ρ.map_mul γ δ) ((Θ S K L hKL hL p).symm v)
    exact (congrArg (Θ S K L hKL hL p) h).trans
      (congrArg (fun y => Θ S K L hKL hL p ((cyclotomicQuotientH2Rep S K L p).ρ γ y)) ((Θ S K L hKL hL p).symm_apply_apply _).symm)

def H2Rep : Rep (ZMod p) ↥K.fixingSubgroup := Rep.of (H2ρ S K L hKL hL p)

theorem H2Rep_ρ_apply (γ : ↥K.fixingSubgroup) (v : H2Rep S K L hKL hL p) :
    (H2Rep S K L hKL hL p).ρ γ v = Θ S K L hKL hL p ((cyclotomicQuotientH2Rep S K L p).ρ γ ((Θ S K L hKL hL p).symm v)) := rfl

theorem H2Rep_ρ_mk (γ : ↥K.fixingSubgroup) (w w' : ↥(levelCocyclesSr₂ L.fixingSubgroup.subtype S (μ L p))) (hb : Block₂ S L p (γ : Γ) w w') :
    (H2Rep S K L hKL hL p).ρ γ (continuousH2Srπ L.fixingSubgroup.subtype S _ w) = continuousH2Srπ L.fixingSubgroup.subtype S _ w' :=
  Θ_equiv S K L hKL hL p γ _ w w' (LinearEquiv.apply_symm_apply _ _) hb

theorem H2Rep_ρ_eq_one_of_mem (γ : ↥K.fixingSubgroup) (hγ : (γ : Γ) ∈ L.fixingSubgroup) : (H2Rep S K L hKL hL p).ρ γ = 1 :=
  LinearMap.ext fun v => by
    change Θ S K L hKL hL p ((cyclotomicQuotientH2Rep S K L p).ρ γ ((Θ S K L hKL hL p).symm v)) = v
    have h1 := LinearMap.congr_fun (cyclotomicQuotientH2Rep_ρ_eq_one_of_mem S K L p γ hγ) ((Θ S K L hKL hL p).symm v)
    exact (congrArg (Θ S K L hKL hL p) h1).trans ((Θ S K L hKL hL p).apply_symm_apply v)

end NumberField.LevelArith.EQBK
p2m_reactivate "P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith.EQBK"
p2m_reactivate "P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith.EQBK"
p2m_reactivate "P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith.EQBK"

end
p2m_reactivate "P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith.EQBK"

noncomputable section

namespace NumberField
p2m_export "NumberField" "mk place RingOfIntegers RingOfIntegers.mapRingEquiv LevelArith.exists_continuousH1Sr_sUnitsMaxRep_linearMap_sClassGroupRep_injective_natural LevelArith.exists_continuousH1Sr_sUnitsMaxRep_linearMap_sClassGroupRep_injective LevelArith.exists_restrict_and_torsionBy_sClassGroupRep_linearEquiv_sClassTorsionP LevelArith.exists_placesAbove_inr_equiv_primesOver LevelArith.nonempty_repTorsionP_iso_repModP"
namespace LevelArith
p2m_export "NumberField.LevelArith" "levelField LevelGal levelFieldEquiv coe_levelFieldEquiv coe_levelFieldEquiv_symm levelGal levelGal_apply_coe modP modP_apply_mk repModP repTorsionP ringOfIntegersAut classGroupAut classGroupRep placesOverPrimes mem_placesOverPrimes_iff placesOverPrimes_finite sClassGroupRep sClassTorsionP IsNormalLevel orbitQuotientAction placesAbove placesRep sUnitsMax sUnitsMaxStable mem_sUnitsMaxStable_iff sUnitsMaxStable_le sUnitsMaxRep sUnitsMaxRep.val exists_continuousH1Sr_sUnitsMaxRep_linearMap_sClassGroupRep_injective_natural exists_continuousH1Sr_sUnitsMaxRep_linearMap_sClassGroupRep_injective exists_restrict_and_torsionBy_sClassGroupRep_linearEquiv_sClassTorsionP exists_placesAbove_inr_equiv_primesOver nonempty_repTorsionP_iso_repModP sUnitsMaxStable_eq_sUnitsMax"
namespace EQBK
p2m_open "NumberField.LevelArith NumberField~mem_placesOverPrimes_iff~placesOverPrimes"

p2m_open "groupCohomology CategoryTheory IsDedekindDomain P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.IsDedekindDomain ExtCitation"
p2m_open_scoped "NumberField P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith Pointwise"

variable (S : Finset Nat.Primes) (K L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hKL : K ≤ L) (hL : L.IsUnramifiedOutside S)
  [FiniteDimensional ℚ ↥K] [FiniteDimensional ℚ ↥L] [Normal ↥K ↥(levelField K L hKL)]
  (hnorm : ∀ g ∈ K.fixingSubgroup, ∀ s ∈ L.fixingSubgroup, g * s * g⁻¹ ∈ L.fixingSubgroup)
  (p : ℕ) [Fact p.Prime] (hpS : pPrime p ∈ S) (h4 : p = 2 → ∃ i ∈ L, i ^ 2 = -1)
  [(L.fixingSubgroup.subgroupOf K.fixingSubgroup).Normal] [(L.fixingSubgroup.subgroupOf K.fixingSubgroup).FiniteIndex]

local notation "Γ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

abbrev Xp : Type := ↥(X S L) ⧸ ((p : ℤ) • (⊤ : Submodule ℤ ↥(X S L)))

def ι : Xp S L p →ₗ[ZMod p] V₂ S L p := Classical.choose (groupCohomology.exists_kummerBrauer_maps_continuousH2Sr_cyclotomic_natural S hpS L hL h4 (p := p))

def invL : V₂ S L p →ₗ[ZMod p] (↥(placesOverPrimes ↥L (S : Set Nat.Primes)) → ZMod p) :=
  Classical.choose (Classical.choose_spec (groupCohomology.exists_kummerBrauer_maps_continuousH2Sr_cyclotomic_natural S hpS L hL h4 (p := p)))

end NumberField.LevelArith.EQBK
p2m_reactivate "P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith.EQBK"
p2m_reactivate "P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith.EQBK"
p2m_reactivate "P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith.EQBK"

end
p2m_reactivate "P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith.EQBK"

noncomputable section

namespace NumberField
p2m_export "NumberField" "mk place RingOfIntegers RingOfIntegers.mapRingEquiv LevelArith.exists_continuousH1Sr_sUnitsMaxRep_linearMap_sClassGroupRep_injective_natural LevelArith.exists_continuousH1Sr_sUnitsMaxRep_linearMap_sClassGroupRep_injective LevelArith.exists_restrict_and_torsionBy_sClassGroupRep_linearEquiv_sClassTorsionP LevelArith.exists_placesAbove_inr_equiv_primesOver LevelArith.nonempty_repTorsionP_iso_repModP"
namespace LevelArith
p2m_export "NumberField.LevelArith" "levelField LevelGal levelFieldEquiv coe_levelFieldEquiv coe_levelFieldEquiv_symm levelGal levelGal_apply_coe modP modP_apply_mk repModP repTorsionP ringOfIntegersAut classGroupAut classGroupRep placesOverPrimes mem_placesOverPrimes_iff placesOverPrimes_finite sClassGroupRep sClassTorsionP IsNormalLevel orbitQuotientAction placesAbove placesRep sUnitsMax sUnitsMaxStable mem_sUnitsMaxStable_iff sUnitsMaxStable_le sUnitsMaxRep sUnitsMaxRep.val exists_continuousH1Sr_sUnitsMaxRep_linearMap_sClassGroupRep_injective_natural exists_continuousH1Sr_sUnitsMaxRep_linearMap_sClassGroupRep_injective exists_restrict_and_torsionBy_sClassGroupRep_linearEquiv_sClassTorsionP exists_placesAbove_inr_equiv_primesOver nonempty_repTorsionP_iso_repModP sUnitsMaxStable_eq_sUnitsMax"
namespace EQBK
p2m_open "NumberField.LevelArith NumberField~mem_placesOverPrimes_iff~placesOverPrimes"

p2m_open "groupCohomology CategoryTheory IsDedekindDomain P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.IsDedekindDomain ExtCitation"
p2m_open_scoped "NumberField P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith Pointwise"

variable (S : Finset Nat.Primes) (K L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hKL : K ≤ L) (hL : L.IsUnramifiedOutside S)
  [FiniteDimensional ℚ ↥K] [FiniteDimensional ℚ ↥L] [Normal ↥K ↥(levelField K L hKL)]
  (hnorm : ∀ g ∈ K.fixingSubgroup, ∀ s ∈ L.fixingSubgroup, g * s * g⁻¹ ∈ L.fixingSubgroup)
  (p : ℕ) [Fact p.Prime] (hpS : pPrime p ∈ S) (h4 : p = 2 → ∃ i ∈ L, i ^ 2 = -1)
  [(L.fixingSubgroup.subgroupOf K.fixingSubgroup).Normal] [(L.fixingSubgroup.subgroupOf K.fixingSubgroup).FiniteIndex]

local notation "Γ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

theorem hστ (γ : ↥K.fixingSubgroup) : ∀ y : ↥L, (γ : Γ) (y : AlgebraicClosure ℚ) = ((τ K L hKL γ y : ↥L) : AlgebraicClosure ℚ) :=
  fun y => (coe_τ K L hKL γ y).symm

theorem block₁_conjCocycle₁ {σ : Γ} (hσ : Normalizes L σ) (c : cocycles₁ (sUnitsMaxRep S L)) :
    ∀ s s' : ↥L.fixingSubgroup, σ⁻¹ * (s : Γ) * σ = s' →
      sUnitsMaxRep.val S L ((conjCocycle₁ S hσ c : ↥L.fixingSubgroup → sUnitsMaxRep S L) s) =
        σ • sUnitsMaxRep.val S L ((c : ↥L.fixingSubgroup → sUnitsMaxRep S L) s') := by
  intro s s' hs
  have : conjHom hσ s = s' := Subtype.ext hs
  change sUnitsMaxRep.val S L (galES S L σ (c (conjHom hσ s))) = _
  rw [this]
  rfl

theorem ι_equivariant (γ : ↥K.fixingSubgroup) (x : repModP p (XRep S K L hnorm)) :
    ι S L hL p hpS h4 ((repModP p (XRep S K L hnorm)).ρ γ x) = (H2Rep S K L hKL hL p).ρ γ (ι S L hL p hpS h4 x) := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  induction y using X_induction S L with
  | h c hc =>

  have hρ : (repModP p (XRep S K L hnorm)).ρ γ (Submodule.Quotient.mk ⟨(H1π _).hom c, H1π_mem_continuousH1Sr _ S _ hc⟩) =
      Submodule.Quotient.mk ⟨(H1π _).hom (conjCocycle₁ S (normalizes_of_mem K L hnorm γ) c),
        H1π_mem_continuousH1Sr _ S _ (isLevelConstantSr₁_conjCocycle₁ S _ hc)⟩ := by
    change Submodule.Quotient.mk ((XRep S K L hnorm).ρ γ _) = _
    congr 1
    exact Subtype.ext (conjX_mk S K L hnorm γ c hc)
  rw [hρ]

  have kbs := Classical.choose_spec (Classical.choose_spec
    (groupCohomology.exists_kummerBrauer_maps_continuousH2Sr_cyclotomic_natural S hpS L hL h4 (p := p)))
  obtain ⟨w, w', hw, hw', hb⟩ := (kbs.2.2.2 (γ : Γ) (τ K L hKL γ) (hστ K L hKL γ)).2
    ⟨c, hc⟩ ⟨conjCocycle₁ S (normalizes_of_mem K L hnorm γ) c, isLevelConstantSr₁_conjCocycle₁ S _ hc⟩
    (block₁_conjCocycle₁ S L _ c)
  have hw2 : ι S L hL p hpS h4 (Submodule.Quotient.mk ⟨(H1π _).hom c, H1π_mem_continuousH1Sr _ S _ hc⟩) =
      continuousH2Srπ L.fixingSubgroup.subtype S _ w := hw
  have hw2' : ι S L hL p hpS h4 (Submodule.Quotient.mk ⟨(H1π _).hom (conjCocycle₁ S (normalizes_of_mem K L hnorm γ) c),
      H1π_mem_continuousH1Sr _ S _ (isLevelConstantSr₁_conjCocycle₁ S _ hc)⟩) = continuousH2Srπ L.fixingSubgroup.subtype S _ w' := hw'
  exact hw2'.trans ((H2Rep_ρ_mk S K L hKL hL p γ w w' hb).symm.trans (congrArg ((H2Rep S K L hKL hL p).ρ γ) hw2.symm))

def ιHom : repModP p (XRep S K L hnorm) ⟶ H2Rep S K L hKL hL p :=
  Rep.ofHom ⟨ι S L hL p hpS h4, fun γ => LinearMap.ext fun x => ι_equivariant S K L hKL hL hnorm p hpS h4 γ x⟩

end NumberField.LevelArith.EQBK
p2m_reactivate "P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith.EQBK"
p2m_reactivate "P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith.EQBK"
p2m_reactivate "P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith.EQBK"

end
p2m_reactivate "P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith.EQBK"

noncomputable section

namespace NumberField
p2m_export "NumberField" "mk place RingOfIntegers RingOfIntegers.mapRingEquiv LevelArith.exists_continuousH1Sr_sUnitsMaxRep_linearMap_sClassGroupRep_injective_natural LevelArith.exists_continuousH1Sr_sUnitsMaxRep_linearMap_sClassGroupRep_injective LevelArith.exists_restrict_and_torsionBy_sClassGroupRep_linearEquiv_sClassTorsionP LevelArith.exists_placesAbove_inr_equiv_primesOver LevelArith.nonempty_repTorsionP_iso_repModP"
namespace LevelArith
p2m_export "NumberField.LevelArith" "levelField LevelGal levelFieldEquiv coe_levelFieldEquiv coe_levelFieldEquiv_symm levelGal levelGal_apply_coe modP modP_apply_mk repModP repTorsionP ringOfIntegersAut classGroupAut classGroupRep placesOverPrimes mem_placesOverPrimes_iff placesOverPrimes_finite sClassGroupRep sClassTorsionP IsNormalLevel orbitQuotientAction placesAbove placesRep sUnitsMax sUnitsMaxStable mem_sUnitsMaxStable_iff sUnitsMaxStable_le sUnitsMaxRep sUnitsMaxRep.val exists_continuousH1Sr_sUnitsMaxRep_linearMap_sClassGroupRep_injective_natural exists_continuousH1Sr_sUnitsMaxRep_linearMap_sClassGroupRep_injective exists_restrict_and_torsionBy_sClassGroupRep_linearEquiv_sClassTorsionP exists_placesAbove_inr_equiv_primesOver nonempty_repTorsionP_iso_repModP sUnitsMaxStable_eq_sUnitsMax"
namespace EQBK
p2m_open "NumberField.LevelArith NumberField~mem_placesOverPrimes_iff~placesOverPrimes"

p2m_open "groupCohomology CategoryTheory IsDedekindDomain P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.IsDedekindDomain ExtCitation"
p2m_open_scoped "NumberField P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith Pointwise"

variable (S : Finset Nat.Primes) (K L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hKL : K ≤ L) (hL : L.IsUnramifiedOutside S)
  [FiniteDimensional ℚ ↥K] [FiniteDimensional ℚ ↥L] [Normal ↥K ↥(levelField K L hKL)]
  (hnorm : ∀ g ∈ K.fixingSubgroup, ∀ s ∈ L.fixingSubgroup, g * s * g⁻¹ ∈ L.fixingSubgroup)
  (p : ℕ) [Fact p.Prime] (hpS : pPrime p ∈ S) (h4 : p = 2 → ∃ i ∈ L, i ^ 2 = -1)
  [(L.fixingSubgroup.subgroupOf K.fixingSubgroup).Normal] [(L.fixingSubgroup.subgroupOf K.fixingSubgroup).FiniteIndex]

local notation "Γ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

theorem valuation_placePull (γ : ↥K.fixingSubgroup) (v' : ↥(placesOverPrimes ↥L (S : Set Nat.Primes))) (y : ↥L) :
    ((v'.1).valuation ↥L) (τ K L hKL γ y) = ((placePull S K L hKL γ v').1).valuation ↥L y := by
  have h := IsDedekindDomain.selmerGroup.K3aPf.valuation_map_eq ↥L (ringOfIntegersAut ℚ ↥L (τ K L hKL γ))
    ((τ K L hKL γ : ↥L ≃ₐ[ℚ] ↥L) : ↥L ≃+* ↥L) (fun r => rfl) v'.1 y
  exact h

theorem μ_ρ_conjHom {σ : Γ} (hσ : Normalizes L σ) (s : ↥L.fixingSubgroup) : (μ L p).ρ (conjHom hσ s) = (μ L p).ρ s := by
  have hχ : cycloChar p (σ⁻¹ * (s : Γ) * σ) = cycloChar p s := by
    rw [map_mul, map_mul, map_inv, mul_comm, ← mul_assoc, mul_inv_cancel, one_mul]
  apply LinearMap.ext; intro x
  change (Representation.twist (Rep.trivial (ZMod p) ↥L.fixingSubgroup (ZMod p)).ρ ((cycloChar p).comp L.fixingSubgroup.subtype)) (conjHom hσ s) x =
    (Representation.twist (Rep.trivial (ZMod p) ↥L.fixingSubgroup (ZMod p)).ρ ((cycloChar p).comp L.fixingSubgroup.subtype)) s x
  have hu : ((cycloChar p).comp L.fixingSubgroup.subtype) (conjHom hσ s) = ((cycloChar p).comp L.fixingSubgroup.subtype) s := by
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply]
    exact hχ
  rw [Representation.twist_apply_apply, Representation.twist_apply_apply, Rep.trivial_ρ_apply, Rep.trivial_ρ_apply, hu]

def conjCocycle₂ {σ : Γ} (hσ : Normalizes L σ) (w : ↥(levelCocyclesSr₂ L.fixingSubgroup.subtype S (μ L p))) :
    ↥(levelCocyclesSr₂ L.fixingSubgroup.subtype S (μ L p)) :=
  ⟨fun st => ((cycloChar p σ : (ZMod p)ˣ) : ZMod p) * (w : ↥L.fixingSubgroup × ↥L.fixingSubgroup → ZMod p) (conjHom hσ st.1, conjHom hσ st.2), by
    obtain ⟨hw1, hw2⟩ := (mem_levelCocyclesSr₂_iff _ S _ _).1 w.2
    refine (mem_levelCocyclesSr₂_iff _ S _ _).2 ⟨?_, ?_⟩
    · rw [mem_cocycles₂_iff] at hw1 ⊢
      intro g h j
      have hh := hw1 (conjHom hσ g) (conjHom hσ h) (conjHom hσ j)
      rw [← map_mul, ← map_mul, μ_ρ_conjHom L p hσ] at hh
      set c : ZMod p := ((cycloChar p σ : (ZMod p)ˣ) : ZMod p)
      change c * (w : _ → ZMod p) (conjHom hσ (g * h), conjHom hσ j) + c * (w : _ → ZMod p) (conjHom hσ g, conjHom hσ h) =
        (μ L p).ρ g (c * (w : _ → ZMod p) (conjHom hσ h, conjHom hσ j)) + c * (w : _ → ZMod p) (conjHom hσ g, conjHom hσ (h * j))
      have hlin : ∀ y : ZMod p, (μ L p).ρ g (c * y) = c * (μ L p).ρ g y := fun y => by
        rw [← smul_eq_mul, map_smul, smul_eq_mul]
      rw [hlin, ← mul_add, ← mul_add, hh]
    · obtain ⟨F, hF, hc⟩ := hw2
      refine ⟨F.map (σ : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ), hF.map_algEquiv σ, fun g g' s s' hs hs' => ?_⟩
      change _ * (w : _ → ZMod p) (conjHom hσ (g * s), conjHom hσ (g' * s')) = _ * (w : _ → ZMod p) (conjHom hσ g, conjHom hσ g')
      rw [map_mul, map_mul]
      congr 1
      have hfix : ∀ s : ↥L.fixingSubgroup, L.fixingSubgroup.subtype s ∈ (F.map (σ : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ)).fixingSubgroup →
          L.fixingSubgroup.subtype (conjHom hσ s) ∈ F.fixingSubgroup := fun s hs => by
        rw [Subgroup.coe_subtype, conjHom_coe, IntermediateField.mem_fixingSubgroup_iff]
        intro x hx
        have hs' := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hs (σ x) ⟨x, hx, rfl⟩
        change (σ⁻¹ * (s : Γ) * σ) x = x
        rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply]
        change σ⁻¹ ((L.fixingSubgroup.subtype s) (σ x)) = x
        rw [hs']
        exact σ.symm_apply_apply x
      exact hc _ _ _ _ (hfix s hs) (hfix s' hs')⟩

theorem conjCocycle₂_block {σ : Γ} (hσ : Normalizes L σ) (w : ↥(levelCocyclesSr₂ L.fixingSubgroup.subtype S (μ L p))) :
    Block₂ S L p σ w (conjCocycle₂ S L p hσ w) := by
  intro s t s' t' hs ht
  have h1 : conjHom hσ s = s' := Subtype.ext hs
  have h2 : conjHom hσ t = t' := Subtype.ext ht
  change _ * (w : _ → ZMod p) (conjHom hσ s, conjHom hσ t) = _
  rw [h1, h2]

include hnorm in

theorem inv_equivariant (γ : ↥K.fixingSubgroup) (a : H2Rep S K L hKL hL p) :
    invL S L hL p hpS h4 ((H2Rep S K L hKL hL p).ρ γ a) = (PlRep S K L hKL p).ρ γ (invL S L hL p hpS h4 a) := by
  obtain ⟨w, rfl⟩ := continuousH2Srπ_surjective L.fixingSubgroup.subtype S (μ L p) a
  have kbs := Classical.choose_spec (Classical.choose_spec
    (groupCohomology.exists_kummerBrauer_maps_continuousH2Sr_cyclotomic_natural S hpS L hL h4 (p := p)))
  let w' := conjCocycle₂ S L p (normalizes_of_mem K L hnorm γ) w
  have hρ : (H2Rep S K L hKL hL p).ρ γ (continuousH2Srπ L.fixingSubgroup.subtype S _ w) = continuousH2Srπ L.fixingSubgroup.subtype S _ w' :=
    H2Rep_ρ_mk S K L hKL hL p γ w w' (conjCocycle₂_block S L p _ w)
  rw [hρ]
  funext v'
  have hnat : invL S L hL p hpS h4 (continuousH2Srπ L.fixingSubgroup.subtype S _ w') v' =
      invL S L hL p hpS h4 (continuousH2Srπ L.fixingSubgroup.subtype S _ w) (placePull S K L hKL γ v') :=
    (kbs.2.2.2 (γ : Γ) (τ K L hKL γ) (hστ K L hKL γ)).1 w w' (conjCocycle₂_block S L p _ w) (placePull S K L hKL γ v') v'
      (fun y => valuation_placePull S K L hKL γ v' y)
  exact hnat

def invHom : H2Rep S K L hKL hL p ⟶ PlRep S K L hKL p :=
  Rep.ofHom ⟨invL S L hL p hpS h4, fun γ => LinearMap.ext fun a => inv_equivariant S K L hKL hL hnorm p hpS h4 γ a⟩

end NumberField.LevelArith.EQBK
p2m_reactivate "P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith.EQBK"
p2m_reactivate "P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith.EQBK"
p2m_reactivate "P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith.EQBK"

end
p2m_reactivate "P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith.EQBK"

noncomputable section

namespace NumberField
p2m_export "NumberField" "mk place RingOfIntegers RingOfIntegers.mapRingEquiv LevelArith.exists_continuousH1Sr_sUnitsMaxRep_linearMap_sClassGroupRep_injective_natural LevelArith.exists_continuousH1Sr_sUnitsMaxRep_linearMap_sClassGroupRep_injective LevelArith.exists_restrict_and_torsionBy_sClassGroupRep_linearEquiv_sClassTorsionP LevelArith.exists_placesAbove_inr_equiv_primesOver LevelArith.nonempty_repTorsionP_iso_repModP"
namespace LevelArith
p2m_export "NumberField.LevelArith" "levelField LevelGal levelFieldEquiv coe_levelFieldEquiv coe_levelFieldEquiv_symm levelGal levelGal_apply_coe modP modP_apply_mk repModP repTorsionP ringOfIntegersAut classGroupAut classGroupRep placesOverPrimes mem_placesOverPrimes_iff placesOverPrimes_finite sClassGroupRep sClassTorsionP IsNormalLevel orbitQuotientAction placesAbove placesRep sUnitsMax sUnitsMaxStable mem_sUnitsMaxStable_iff sUnitsMaxStable_le sUnitsMaxRep sUnitsMaxRep.val exists_continuousH1Sr_sUnitsMaxRep_linearMap_sClassGroupRep_injective_natural exists_continuousH1Sr_sUnitsMaxRep_linearMap_sClassGroupRep_injective exists_restrict_and_torsionBy_sClassGroupRep_linearEquiv_sClassTorsionP exists_placesAbove_inr_equiv_primesOver nonempty_repTorsionP_iso_repModP sUnitsMaxStable_eq_sUnitsMax"
namespace EQBK
p2m_open "NumberField.LevelArith NumberField~mem_placesOverPrimes_iff~placesOverPrimes"

p2m_open "groupCohomology CategoryTheory IsDedekindDomain P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.IsDedekindDomain ExtCitation CategoryTheory.Limits CategoryTheory.MonoidalCategory.Limits"
p2m_open_scoped "NumberField P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith Pointwise"

variable (S : Finset Nat.Primes) (K L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hKL : K ≤ L) (hL : L.IsUnramifiedOutside S)
  [FiniteDimensional ℚ ↥K] [FiniteDimensional ℚ ↥L] [Normal ↥K ↥(levelField K L hKL)]
  (hnorm : ∀ g ∈ K.fixingSubgroup, ∀ s ∈ L.fixingSubgroup, g * s * g⁻¹ ∈ L.fixingSubgroup)
  (p : ℕ) [Fact p.Prime] (hpS : pPrime p ∈ S) (h4 : p = 2 → ∃ i ∈ L, i ^ 2 = -1)
  [(L.fixingSubgroup.subgroupOf K.fixingSubgroup).Normal] [(L.fixingSubgroup.subgroupOf K.fixingSubgroup).FiniteIndex]

local notation "Γ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

theorem kb_exact :
    Function.Injective (ι S L hL p hpS h4) ∧ LinearMap.range (ι S L hL p hpS h4) = LinearMap.ker (invL S L hL p hpS h4) ∧
    (∀ f, f ∈ LinearMap.range (invL S L hL p hpS h4) ↔ ∑ᶠ w, f w = 0) := by
  have kbs := Classical.choose_spec (Classical.choose_spec
    (groupCohomology.exists_kummerBrauer_maps_continuousH2Sr_cyclotomic_natural S hpS L hL h4 (p := p)))
  exact ⟨kbs.1, kbs.2.1, kbs.2.2.1⟩

def Pl0Rep : Rep (ZMod p) ↥K.fixingSubgroup :=
  Rep.of ((PlRep S K L hKL p).ρ.subrepresentation (LinearMap.range (invL S L hL p hpS h4)) fun γ => by
    rintro _ ⟨a, rfl⟩
    exact ⟨(H2Rep S K L hKL hL p).ρ γ a, inv_equivariant S K L hKL hL hnorm p hpS h4 γ a⟩)

def qHom : H2Rep S K L hKL hL p ⟶ Pl0Rep S K L hKL hL hnorm p hpS h4 :=
  Rep.ofHom ⟨LinearMap.codRestrict _ (invL S L hL p hpS h4) (fun a => LinearMap.mem_range_self _ a), fun γ => LinearMap.ext fun a =>
    Subtype.ext (inv_equivariant S K L hKL hL hnorm p hpS h4 γ a)⟩

def jHom : Pl0Rep S K L hKL hL hnorm p hpS h4 ⟶ PlRep S K L hKL p :=
  Rep.ofHom ⟨Submodule.subtype _, fun γ => rfl⟩

theorem ιHom_qHom : ιHom S K L hKL hL hnorm p hpS h4 ≫ qHom S K L hKL hL hnorm p hpS h4 = 0 := by
  apply Rep.hom_ext
  refine DFunLike.ext _ _ fun x => Subtype.ext ?_
  change invL S L hL p hpS h4 (ι S L hL p hpS h4 x) = 0
  have : ι S L hL p hpS h4 x ∈ LinearMap.ker (invL S L hL p hpS h4) := (kb_exact S L hL p hpS h4).2.1 ▸ LinearMap.mem_range_self _ x
  exact this

def SES₁ : ShortComplex (Rep.{0} (ZMod p) ↥K.fixingSubgroup) :=
  ShortComplex.mk (ιHom S K L hKL hL hnorm p hpS h4) (qHom S K L hKL hL hnorm p hpS h4) (ιHom_qHom S K L hKL hL hnorm p hpS h4)

theorem SES₁_shortExact : (SES₁ S K L hKL hL hnorm p hpS h4).ShortExact := by
  haveI : Mono (SES₁ S K L hKL hL hnorm p hpS h4).f := (Rep.mono_iff_injective _).2 (kb_exact S L hL p hpS h4).1
  haveI : Epi (SES₁ S K L hKL hL hnorm p hpS h4).g := (Rep.epi_iff_surjective _).2 fun y => by
    obtain ⟨a, ha⟩ := y.2
    exact ⟨a, Subtype.ext ha⟩
  refine ShortComplex.ShortExact.mk ?_
  rw [← ShortComplex.exact_map_iff_of_faithful _ (forget₂ (Rep (ZMod p) ↥K.fixingSubgroup) (ModuleCat (ZMod p))),
    ShortComplex.moduleCat_exact_iff_range_eq_ker]
  change LinearMap.range (ι S L hL p hpS h4) = LinearMap.ker (LinearMap.codRestrict _ (invL S L hL p hpS h4) _)
  rw [LinearMap.ker_codRestrict]
  exact (kb_exact S L hL p hpS h4).2.1

end NumberField.LevelArith.EQBK
p2m_reactivate "P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith.EQBK"
p2m_reactivate "P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith.EQBK"
p2m_reactivate "P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith.EQBK"

end
p2m_reactivate "P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith.EQBK"

noncomputable section

namespace NumberField
p2m_export "NumberField" "mk place RingOfIntegers RingOfIntegers.mapRingEquiv LevelArith.exists_continuousH1Sr_sUnitsMaxRep_linearMap_sClassGroupRep_injective_natural LevelArith.exists_continuousH1Sr_sUnitsMaxRep_linearMap_sClassGroupRep_injective LevelArith.exists_restrict_and_torsionBy_sClassGroupRep_linearEquiv_sClassTorsionP LevelArith.exists_placesAbove_inr_equiv_primesOver LevelArith.nonempty_repTorsionP_iso_repModP"
namespace LevelArith
p2m_export "NumberField.LevelArith" "levelField LevelGal levelFieldEquiv coe_levelFieldEquiv coe_levelFieldEquiv_symm levelGal levelGal_apply_coe modP modP_apply_mk repModP repTorsionP ringOfIntegersAut classGroupAut classGroupRep placesOverPrimes mem_placesOverPrimes_iff placesOverPrimes_finite sClassGroupRep sClassTorsionP IsNormalLevel orbitQuotientAction placesAbove placesRep sUnitsMax sUnitsMaxStable mem_sUnitsMaxStable_iff sUnitsMaxStable_le sUnitsMaxRep sUnitsMaxRep.val exists_continuousH1Sr_sUnitsMaxRep_linearMap_sClassGroupRep_injective_natural exists_continuousH1Sr_sUnitsMaxRep_linearMap_sClassGroupRep_injective exists_restrict_and_torsionBy_sClassGroupRep_linearEquiv_sClassTorsionP exists_placesAbove_inr_equiv_primesOver nonempty_repTorsionP_iso_repModP sUnitsMaxStable_eq_sUnitsMax"
namespace EQBK
p2m_open "NumberField.LevelArith NumberField~mem_placesOverPrimes_iff~placesOverPrimes"

p2m_open "groupCohomology CategoryTheory IsDedekindDomain P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.IsDedekindDomain ExtCitation CategoryTheory.Limits CategoryTheory.MonoidalCategory.Limits"
p2m_open_scoped "NumberField P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith Pointwise"

variable (S : Finset Nat.Primes) (K L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hKL : K ≤ L) (hL : L.IsUnramifiedOutside S)
  [FiniteDimensional ℚ ↥K] [FiniteDimensional ℚ ↥L] [Normal ↥K ↥(levelField K L hKL)]
  (hnorm : ∀ g ∈ K.fixingSubgroup, ∀ s ∈ L.fixingSubgroup, g * s * g⁻¹ ∈ L.fixingSubgroup)
  (p : ℕ) [Fact p.Prime] (hpS : pPrime p ∈ S) (h4 : p = 2 → ∃ i ∈ L, i ^ 2 = -1)
  [(L.fixingSubgroup.subgroupOf K.fixingSubgroup).Normal] [(L.fixingSubgroup.subgroupOf K.fixingSubgroup).FiniteIndex]

local notation "Γ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

scoped instance finite_placesOverPrimes : Finite ↥(placesOverPrimes ↥L (S : Set Nat.Primes)) := (placesOverPrimes_finite ↥L S).to_subtype

def placePullEquiv (γ : ↥K.fixingSubgroup) : ↥(placesOverPrimes ↥L (S : Set Nat.Primes)) ≃ ↥(placesOverPrimes ↥L (S : Set Nat.Primes)) where
  toFun := placePull S K L hKL γ
  invFun := placePull S K L hKL γ⁻¹
  left_inv w := by rw [← placePull_mul, mul_inv_cancel, placePull_one]
  right_inv w := by rw [← placePull_mul, inv_mul_cancel, placePull_one]

def sumLin : (↥(placesOverPrimes ↥L (S : Set Nat.Primes)) → ZMod p) →ₗ[ZMod p] ZMod p where
  toFun f := finsum f
  map_add' f g := finsum_add_distrib (Set.toFinite _) (Set.toFinite _)
  map_smul' c f := (mul_finsum f c).symm

def sumHom : PlRep S K L hKL p ⟶ Rep.trivial (ZMod p) ↥K.fixingSubgroup (ZMod p) :=
  Rep.ofHom ⟨sumLin S L p,
    fun γ => LinearMap.ext fun f => by
      change ∑ᶠ w, f (placePull S K L hKL γ w) = (Rep.trivial (ZMod p) ↥K.fixingSubgroup (ZMod p)).ρ γ (∑ᶠ w, f w)
      rw [Rep.trivial_ρ_apply]
      exact finsum_comp_equiv (placePullEquiv S K L hKL γ)⟩

theorem sumHom_apply (f : PlRep S K L hKL p) : (sumHom S K L hKL p).hom f = ∑ᶠ w, f w := rfl

theorem jHom_sumHom : jHom S K L hKL hL hnorm p hpS h4 ≫ sumHom S K L hKL p = 0 := by
  apply Rep.hom_ext
  refine DFunLike.ext _ _ fun f => ?_
  change ∑ᶠ w, (f.1 : _ → ZMod p) w = 0
  exact ((kb_exact S L hL p hpS h4).2.2 f.1).1 f.2

def SES₂ : ShortComplex (Rep.{0} (ZMod p) ↥K.fixingSubgroup) :=
  ShortComplex.mk (jHom S K L hKL hL hnorm p hpS h4) (sumHom S K L hKL p) (jHom_sumHom S K L hKL hL hnorm p hpS h4)

include hpS in

theorem exists_place : ∃ w : HeightOneSpectrum (𝓞 ↥L), w ∈ placesOverPrimes ↥L (S : Set Nat.Primes) := by
  have hp : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 (Fact.out : p.Prime)
  haveI hPmax : (Ideal.span {(p : ℤ)}).IsMaximal := ((Ideal.span_singleton_prime hp.ne_zero).2 hp).isMaximal (by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact hp.ne_zero)
  obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 ↥L) (Ideal.span {(p : ℤ)})
    (by rw [(RingHom.injective_iff_ker_eq_bot _).1 (algebraMap ℤ (𝓞 ↥L)).injective_int]; exact bot_le)
  have hpQ : ((p : ℕ) : 𝓞 ↥L) ∈ Q := by
    have : (p : ℤ) ∈ Q.comap (algebraMap ℤ (𝓞 ↥L)) := hQP ▸ Ideal.subset_span rfl
    simpa using this
  refine ⟨⟨Q, hQ.isPrime, fun h => ?_⟩, (mem_placesOverPrimes_iff _ _ _).2 ⟨pPrime p, hpS, hpQ⟩⟩
  rw [h, Ideal.comap_bot_of_injective _ (algebraMap ℤ (𝓞 ↥L)).injective_int] at hQP
  exact hp.ne_zero (Ideal.span_singleton_eq_bot.1 hQP.symm)

theorem SES₂_shortExact : (SES₂ S K L hKL hL hnorm p hpS h4).ShortExact := by
  haveI : Mono (SES₂ S K L hKL hL hnorm p hpS h4).f := (Rep.mono_iff_injective _).2 Subtype.val_injective
  haveI : Epi (SES₂ S K L hKL hL hnorm p hpS h4).g := (Rep.epi_iff_surjective _).2 fun c => by
    obtain ⟨w₀, hw₀⟩ := exists_place S L p hpS
    classical
    refine ⟨Pi.single (⟨w₀, hw₀⟩ : ↥(placesOverPrimes ↥L (S : Set Nat.Primes))) c, ?_⟩
    change ∑ᶠ w, (Pi.single (⟨w₀, hw₀⟩ : ↥(placesOverPrimes ↥L (S : Set Nat.Primes))) c : _ → ZMod p) w = c
    rw [finsum_eq_single _ ⟨w₀, hw₀⟩ (fun w hw => Pi.single_eq_of_ne hw _), Pi.single_eq_same]
  refine ShortComplex.ShortExact.mk ?_
  rw [← ShortComplex.exact_map_iff_of_faithful _ (forget₂ (Rep (ZMod p) ↥K.fixingSubgroup) (ModuleCat (ZMod p))),
    ShortComplex.moduleCat_exact_iff_range_eq_ker]
  change LinearMap.range (Submodule.subtype _) = LinearMap.ker _
  rw [Submodule.range_subtype]
  ext f
  show f ∈ _ ↔ (∑ᶠ w, f w) = 0
  exact (kb_exact S L hL p hpS h4).2.2 f

end NumberField.LevelArith.EQBK
p2m_reactivate "P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith.EQBK"
p2m_reactivate "P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith.EQBK"
p2m_reactivate "P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith.EQBK"

end
p2m_reactivate "P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith.EQBK"

noncomputable section

namespace NumberField
p2m_export "NumberField" "mk place RingOfIntegers RingOfIntegers.mapRingEquiv LevelArith.exists_continuousH1Sr_sUnitsMaxRep_linearMap_sClassGroupRep_injective_natural LevelArith.exists_continuousH1Sr_sUnitsMaxRep_linearMap_sClassGroupRep_injective LevelArith.exists_restrict_and_torsionBy_sClassGroupRep_linearEquiv_sClassTorsionP LevelArith.exists_placesAbove_inr_equiv_primesOver LevelArith.nonempty_repTorsionP_iso_repModP"
namespace LevelArith
p2m_export "NumberField.LevelArith" "levelField LevelGal levelFieldEquiv coe_levelFieldEquiv coe_levelFieldEquiv_symm levelGal levelGal_apply_coe modP modP_apply_mk repModP repTorsionP ringOfIntegersAut classGroupAut classGroupRep placesOverPrimes mem_placesOverPrimes_iff placesOverPrimes_finite sClassGroupRep sClassTorsionP IsNormalLevel orbitQuotientAction placesAbove placesRep sUnitsMax sUnitsMaxStable mem_sUnitsMaxStable_iff sUnitsMaxStable_le sUnitsMaxRep sUnitsMaxRep.val exists_continuousH1Sr_sUnitsMaxRep_linearMap_sClassGroupRep_injective_natural exists_continuousH1Sr_sUnitsMaxRep_linearMap_sClassGroupRep_injective exists_restrict_and_torsionBy_sClassGroupRep_linearEquiv_sClassTorsionP exists_placesAbove_inr_equiv_primesOver nonempty_repTorsionP_iso_repModP sUnitsMaxStable_eq_sUnitsMax"
namespace EQBK
p2m_open "NumberField.LevelArith NumberField~mem_placesOverPrimes_iff~placesOverPrimes"

p2m_open "groupCohomology CategoryTheory IsDedekindDomain P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.IsDedekindDomain ExtCitation CategoryTheory.Limits CategoryTheory.MonoidalCategory.Limits"
p2m_open_scoped "NumberField P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith Pointwise"

variable (S : Finset Nat.Primes) (K L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hKL : K ≤ L) (hL : L.IsUnramifiedOutside S)
  [FiniteDimensional ℚ ↥K] [FiniteDimensional ℚ ↥L] [Normal ↥K ↥(levelField K L hKL)]
  (hnorm : ∀ g ∈ K.fixingSubgroup, ∀ s ∈ L.fixingSubgroup, g * s * g⁻¹ ∈ L.fixingSubgroup)
  (p : ℕ) [Fact p.Prime] (hcop : (L.fixingSubgroup.relIndex K.fixingSubgroup).Coprime p) (hpS : pPrime p ∈ S) (h4 : p = 2 → ∃ i ∈ L, i ^ 2 = -1)
  [(L.fixingSubgroup.subgroupOf K.fixingSubgroup).Normal] [(L.fixingSubgroup.subgroupOf K.fixingSubgroup).FiniteIndex]

local notation "Γ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

scoped instance fd_PlRep : FiniteDimensional (ZMod p) (PlRep S K L hKL p) := by
  change Module.Finite (ZMod p) (↥(placesOverPrimes ↥L (S : Set Nat.Primes)) → ZMod p)
  infer_instance

scoped instance fd_Pl0Rep : FiniteDimensional (ZMod p) (Pl0Rep S K L hKL hL hnorm p hpS h4) := by
  change Module.Finite (ZMod p) ↥(LinearMap.range (invL S L hL p hpS h4))
  infer_instance

theorem fd_Xp [Finite ↥(X S L)] : FiniteDimensional (ZMod p) (Xp S L p) := by
  haveI : Finite (Xp S L p) := Finite.of_surjective _ (Submodule.Quotient.mk_surjective _)
  exact Module.Finite.of_finite

include hpS h4 in
theorem fd_H2Rep [Finite ↥(X S L)] : FiniteDimensional (ZMod p) (H2Rep S K L hKL hL p) := by
  change Module.Finite (ZMod p) (V₂ S L p)
  haveI := fd_Xp S L p

  haveI : Module.Finite (ZMod p) ↥(LinearMap.range (ι S L hL p hpS h4)) := inferInstance
  haveI : Module.Finite (ZMod p) (V₂ S L p ⧸ LinearMap.range (ι S L hL p hpS h4)) := by
    rw [(kb_exact S L hL p hpS h4).2.1]
    exact Module.Finite.equiv ((invL S L hL p hpS h4).quotKerEquivRange).symm
  exact Module.Finite.of_submodule_quotient (LinearMap.range (ι S L hL p hpS h4))

scoped instance finite_quot : Finite (↥K.fixingSubgroup ⧸ (L.fixingSubgroup.subgroupOf K.fixingSubgroup)) := Subgroup.finite_quotient_of_finiteIndex

omit [(L.fixingSubgroup.subgroupOf K.fixingSubgroup).Normal] in
include hcop in
theorem hcop' : (Nat.card (↥K.fixingSubgroup ⧸ (L.fixingSubgroup.subgroupOf K.fixingSubgroup))).Coprime p := hcop

include hcop in
theorem split₁ [Finite ↥(X S L)] :
    Nonempty (H2Rep S K L hKL hL p ≅ repModP p (XRep S K L hnorm) ⊞ Pl0Rep S K L hKL hL hnorm p hpS h4) := by
  haveI : FiniteDimensional (ZMod p) (SES₁ S K L hKL hL hnorm p hpS h4).X₂ := fd_H2Rep S K L hKL hL p hpS h4
  exact Rep.nonempty_iso_biprod_of_shortExact_of_trivial_of_coprime (L.fixingSubgroup.subgroupOf K.fixingSubgroup) (hcop' K L p hcop) (SES₁ S K L hKL hL hnorm p hpS h4)
    (SES₁_shortExact S K L hKL hL hnorm p hpS h4) (fun s hs => H2Rep_ρ_eq_one_of_mem S K L hKL hL p s (Subgroup.mem_subgroupOf.1 hs))

include hcop in
theorem split₂ :
    Nonempty (PlRep S K L hKL p ≅ Pl0Rep S K L hKL hL hnorm p hpS h4 ⊞ Rep.trivial (ZMod p) ↥K.fixingSubgroup (ZMod p)) := by
  haveI : FiniteDimensional (ZMod p) (SES₂ S K L hKL hL hnorm p hpS h4).X₂ := (inferInstance : FiniteDimensional (ZMod p) (PlRep S K L hKL p))
  exact Rep.nonempty_iso_biprod_of_shortExact_of_trivial_of_coprime (L.fixingSubgroup.subgroupOf K.fixingSubgroup) (hcop' K L p hcop) (SES₂ S K L hKL hL hnorm p hpS h4)
    (SES₂_shortExact S K L hKL hL hnorm p hpS h4) (fun s hs => PlRep_ρ_eq_one_of_mem S K L hKL p s (Subgroup.mem_subgroupOf.1 hs))

def ΘIso : cyclotomicQuotientH2Rep S K L p ≅ H2Rep S K L hKL hL p :=
  Rep.mkIso (Representation.Equiv.mk (Θ S K L hKL hL p) fun γ => LinearMap.ext fun a => by
    change Θ S K L hKL hL p ((cyclotomicQuotientH2Rep S K L p).ρ γ a) =
      Θ S K L hKL hL p ((cyclotomicQuotientH2Rep S K L p).ρ γ ((Θ S K L hKL hL p).symm (Θ S K L hKL hL p a)))
    rw [LinearEquiv.symm_apply_apply])

include hKL hL hpS h4 in
theorem fd_A₂ [Finite ↥(X S L)] : FiniteDimensional (ZMod p) (cyclotomicQuotientH2Rep S K L p) := by
  haveI : Module.Finite (ZMod p) (V₂ S L p) := fd_H2Rep S K L hKL hL p hpS h4
  exact Module.Finite.equiv (Θ S K L hKL hL p).symm

end NumberField.LevelArith.EQBK
p2m_reactivate "P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith.EQBK"
p2m_reactivate "P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith.EQBK"
p2m_reactivate "P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith.EQBK"

end
p2m_reactivate "P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith.EQBK"

noncomputable section

namespace NumberField
p2m_export "NumberField" "mk place RingOfIntegers RingOfIntegers.mapRingEquiv LevelArith.exists_continuousH1Sr_sUnitsMaxRep_linearMap_sClassGroupRep_injective_natural LevelArith.exists_continuousH1Sr_sUnitsMaxRep_linearMap_sClassGroupRep_injective LevelArith.exists_restrict_and_torsionBy_sClassGroupRep_linearEquiv_sClassTorsionP LevelArith.exists_placesAbove_inr_equiv_primesOver LevelArith.nonempty_repTorsionP_iso_repModP"
namespace LevelArith
p2m_export "NumberField.LevelArith" "levelField LevelGal levelFieldEquiv coe_levelFieldEquiv coe_levelFieldEquiv_symm levelGal levelGal_apply_coe modP modP_apply_mk repModP repTorsionP ringOfIntegersAut classGroupAut classGroupRep placesOverPrimes mem_placesOverPrimes_iff placesOverPrimes_finite sClassGroupRep sClassTorsionP IsNormalLevel orbitQuotientAction placesAbove placesRep sUnitsMax sUnitsMaxStable mem_sUnitsMaxStable_iff sUnitsMaxStable_le sUnitsMaxRep sUnitsMaxRep.val exists_continuousH1Sr_sUnitsMaxRep_linearMap_sClassGroupRep_injective_natural exists_continuousH1Sr_sUnitsMaxRep_linearMap_sClassGroupRep_injective exists_restrict_and_torsionBy_sClassGroupRep_linearEquiv_sClassTorsionP exists_placesAbove_inr_equiv_primesOver nonempty_repTorsionP_iso_repModP sUnitsMaxStable_eq_sUnitsMax"
namespace EQBK
p2m_open "NumberField.LevelArith NumberField~mem_placesOverPrimes_iff~placesOverPrimes"

p2m_open "groupCohomology CategoryTheory IsDedekindDomain P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.IsDedekindDomain ExtCitation CategoryTheory.Limits CategoryTheory.MonoidalCategory.Limits"
p2m_open_scoped "NumberField P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith Pointwise"

variable (S : Finset Nat.Primes) (L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hL : L.IsUnramifiedOutside S) [FiniteDimensional ℚ ↥L]
  (p : ℕ) [Fact p.Prime] (hpS : pPrime p ∈ S)

include hL hpS in

theorem finite_X : Finite ↥(X S L) := by
  obtain ⟨f, hf, -⟩ := NumberField.LevelArith.exists_continuousH1Sr_sUnitsMaxRep_linearMap_sClassGroupRep_injective S hpS L hL (p := p)
  haveI : Finite (sClassGroupRep ↥L ↥L (S : Set Nat.Primes)) := by
    haveI : Finite (classGroupRep ↥L ↥L) := inferInstanceAs (Finite (Additive (ClassGroup (𝓞 ↥L))))
    exact Finite.of_surjective _ (Submodule.Quotient.mk_surjective _)
  exact Finite.of_injective f hf

end NumberField.LevelArith.EQBK
p2m_reactivate "P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith.EQBK"
p2m_reactivate "P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith.EQBK"
p2m_reactivate "P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith.EQBK"

end
p2m_reactivate "P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith.EQBK"

noncomputable section

namespace NumberField
p2m_export "NumberField" "mk place RingOfIntegers RingOfIntegers.mapRingEquiv LevelArith.exists_continuousH1Sr_sUnitsMaxRep_linearMap_sClassGroupRep_injective_natural LevelArith.exists_continuousH1Sr_sUnitsMaxRep_linearMap_sClassGroupRep_injective LevelArith.exists_restrict_and_torsionBy_sClassGroupRep_linearEquiv_sClassTorsionP LevelArith.exists_placesAbove_inr_equiv_primesOver LevelArith.nonempty_repTorsionP_iso_repModP"
namespace LevelArith
p2m_export "NumberField.LevelArith" "levelField LevelGal levelFieldEquiv coe_levelFieldEquiv coe_levelFieldEquiv_symm levelGal levelGal_apply_coe modP modP_apply_mk repModP repTorsionP ringOfIntegersAut classGroupAut classGroupRep placesOverPrimes mem_placesOverPrimes_iff placesOverPrimes_finite sClassGroupRep sClassTorsionP IsNormalLevel orbitQuotientAction placesAbove placesRep sUnitsMax sUnitsMaxStable mem_sUnitsMaxStable_iff sUnitsMaxStable_le sUnitsMaxRep sUnitsMaxRep.val exists_continuousH1Sr_sUnitsMaxRep_linearMap_sClassGroupRep_injective_natural exists_continuousH1Sr_sUnitsMaxRep_linearMap_sClassGroupRep_injective exists_restrict_and_torsionBy_sClassGroupRep_linearEquiv_sClassTorsionP exists_placesAbove_inr_equiv_primesOver nonempty_repTorsionP_iso_repModP sUnitsMaxStable_eq_sUnitsMax"
namespace EQBK
p2m_open "NumberField.LevelArith NumberField~mem_placesOverPrimes_iff~placesOverPrimes"

p2m_open "groupCohomology CategoryTheory IsDedekindDomain P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.IsDedekindDomain ExtCitation CategoryTheory.Limits CategoryTheory.MonoidalCategory.Limits"
p2m_open_scoped "NumberField P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith Pointwise"

variable (S : Finset Nat.Primes) (K L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hKL : K ≤ L) (hL : L.IsUnramifiedOutside S)
  [FiniteDimensional ℚ ↥K] [FiniteDimensional ℚ ↥L] [Normal ↥K ↥(levelField K L hKL)]
  (hnorm : ∀ g ∈ K.fixingSubgroup, ∀ s ∈ L.fixingSubgroup, g * s * g⁻¹ ∈ L.fixingSubgroup)
  (p : ℕ) [Fact p.Prime] (hpS : pPrime p ∈ S)

local notation "Γ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

abbrev ClV : Type := sClassGroupRep ↥L ↥L (S : Set Nat.Primes)

def fX : ↥(X S L) →ₗ[ℤ] ClV S L :=
  Classical.choose (NumberField.LevelArith.exists_continuousH1Sr_sUnitsMaxRep_linearMap_sClassGroupRep_injective_natural S hpS L hL (p := p))

def τ' : ↥K.fixingSubgroup →* (↥L ≃ₐ[ℚ] ↥L) :=
  Classical.choose (NumberField.LevelArith.exists_restrict_and_torsionBy_sClassGroupRep_linearEquiv_sClassTorsionP S K L hKL hnorm (p := p))

theorem τ'_spec : ∀ (γ : ↥K.fixingSubgroup) (y : ↥L), (γ : Γ) (y : AlgebraicClosure ℚ) = ((τ' S K L hKL hnorm p γ y : ↥L) : AlgebraicClosure ℚ) :=
  Classical.choose (Classical.choose_spec (NumberField.LevelArith.exists_restrict_and_torsionBy_sClassGroupRep_linearEquiv_sClassTorsionP S K L hKL hnorm (p := p)))

def eCl : ↥(Submodule.torsionBy ℤ (ClV S L) (p : ℤ)) ≃ₗ[ZMod p] sClassTorsionP K L hKL S p :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec
    (NumberField.LevelArith.exists_restrict_and_torsionBy_sClassGroupRep_linearEquiv_sClassTorsionP S K L hKL hnorm (p := p))))

theorem τ'_eq_τ (γ : ↥K.fixingSubgroup) : τ' S K L hKL hnorm p γ = τ K L hKL γ :=
  AlgEquiv.ext fun y => Subtype.ext (by rw [← τ'_spec, coe_τ])

end NumberField.LevelArith.EQBK
p2m_reactivate "P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith.EQBK"
p2m_reactivate "P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith.EQBK"
p2m_reactivate "P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith.EQBK"

end
p2m_reactivate "P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith.EQBK"

noncomputable section

namespace NumberField
p2m_export "NumberField" "mk place RingOfIntegers RingOfIntegers.mapRingEquiv LevelArith.exists_continuousH1Sr_sUnitsMaxRep_linearMap_sClassGroupRep_injective_natural LevelArith.exists_continuousH1Sr_sUnitsMaxRep_linearMap_sClassGroupRep_injective LevelArith.exists_restrict_and_torsionBy_sClassGroupRep_linearEquiv_sClassTorsionP LevelArith.exists_placesAbove_inr_equiv_primesOver LevelArith.nonempty_repTorsionP_iso_repModP"
namespace LevelArith
p2m_export "NumberField.LevelArith" "levelField LevelGal levelFieldEquiv coe_levelFieldEquiv coe_levelFieldEquiv_symm levelGal levelGal_apply_coe modP modP_apply_mk repModP repTorsionP ringOfIntegersAut classGroupAut classGroupRep placesOverPrimes mem_placesOverPrimes_iff placesOverPrimes_finite sClassGroupRep sClassTorsionP IsNormalLevel orbitQuotientAction placesAbove placesRep sUnitsMax sUnitsMaxStable mem_sUnitsMaxStable_iff sUnitsMaxStable_le sUnitsMaxRep sUnitsMaxRep.val exists_continuousH1Sr_sUnitsMaxRep_linearMap_sClassGroupRep_injective_natural exists_continuousH1Sr_sUnitsMaxRep_linearMap_sClassGroupRep_injective exists_restrict_and_torsionBy_sClassGroupRep_linearEquiv_sClassTorsionP exists_placesAbove_inr_equiv_primesOver nonempty_repTorsionP_iso_repModP sUnitsMaxStable_eq_sUnitsMax"
namespace EQBK
p2m_open "NumberField.LevelArith NumberField~mem_placesOverPrimes_iff~placesOverPrimes"

p2m_open "groupCohomology CategoryTheory IsDedekindDomain P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.IsDedekindDomain ExtCitation CategoryTheory.Limits CategoryTheory.MonoidalCategory.Limits"
p2m_open_scoped "NumberField P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith Pointwise"

variable (S : Finset Nat.Primes) (K L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hKL : K ≤ L) (hL : L.IsUnramifiedOutside S)
  [FiniteDimensional ℚ ↥K] [FiniteDimensional ℚ ↥L] [Normal ↥K ↥(levelField K L hKL)]
  (hnorm : ∀ g ∈ K.fixingSubgroup, ∀ s ∈ L.fixingSubgroup, g * s * g⁻¹ ∈ L.fixingSubgroup)
  (p : ℕ) [Fact p.Prime] (hpS : pPrime p ∈ S)
  [(L.fixingSubgroup.subgroupOf K.fixingSubgroup).Normal] [(L.fixingSubgroup.subgroupOf K.fixingSubgroup).FiniteIndex]

local notation "Γ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

theorem fX_injective : Function.Injective (fX S L hL p hpS) :=
  (Classical.choose_spec (NumberField.LevelArith.exists_continuousH1Sr_sUnitsMaxRep_linearMap_sClassGroupRep_injective_natural S hpS L hL (p := p))).1

theorem fX_map_torsion : Submodule.map (fX S L hL p hpS) (Submodule.torsionBy ℤ ↥(X S L) (p : ℤ)) = Submodule.torsionBy ℤ (ClV S L) (p : ℤ) :=
  (Classical.choose_spec (NumberField.LevelArith.exists_continuousH1Sr_sUnitsMaxRep_linearMap_sClassGroupRep_injective_natural S hpS L hL (p := p))).2.1

theorem fX_mem_torsion (x : ↥(Submodule.torsionBy ℤ ↥(X S L) (p : ℤ))) : fX S L hL p hpS x.1 ∈ Submodule.torsionBy ℤ (ClV S L) (p : ℤ) :=
  fX_map_torsion S L hL p hpS ▸ Submodule.mem_map_of_mem x.2

def gX (x : repTorsionP p (XRep S K L hnorm)) : sClassTorsionP K L hKL S p :=
  eCl S K L hKL hnorm p ⟨fX S L hL p hpS x.1, fX_mem_torsion S L hL p hpS x⟩

def gXAdd : repTorsionP p (XRep S K L hnorm) →+ sClassTorsionP K L hKL S p where
  toFun := gX S K L hKL hL hnorm p hpS
  map_zero' := by
    change eCl S K L hKL hnorm p ⟨fX S L hL p hpS 0, _⟩ = 0
    rw [← map_zero (eCl S K L hKL hnorm p)]
    congr 1
    exact Subtype.ext (map_zero _)
  map_add' x y := by
    change eCl S K L hKL hnorm p ⟨fX S L hL p hpS (x.1 + y.1), _⟩ = eCl S K L hKL hnorm p _ + eCl S K L hKL hnorm p _
    rw [← map_add (eCl S K L hKL hnorm p)]
    congr 1
    exact Subtype.ext (map_add _ _ _)

def gXLin : repTorsionP p (XRep S K L hnorm) →ₗ[ZMod p] sClassTorsionP K L hKL S p := (gXAdd S K L hKL hL hnorm p hpS).toZModLinearMap p

theorem gX_bijective : Function.Bijective (gXLin S K L hKL hL hnorm p hpS) := by
  constructor
  · intro x y h
    have h1 := (eCl S K L hKL hnorm p).injective h
    exact Subtype.ext (fX_injective S L hL p hpS (congrArg Subtype.val h1))
  · intro z
    obtain ⟨w, rfl⟩ := (eCl S K L hKL hnorm p).surjective z
    have hw : w.1 ∈ Submodule.map (fX S L hL p hpS) (Submodule.torsionBy ℤ ↥(X S L) (p : ℤ)) := by
      rw [fX_map_torsion]; exact w.2
    obtain ⟨x, hx, hxw⟩ := hw
    exact ⟨⟨x, hx⟩, congrArg (eCl S K L hKL hnorm p) (Subtype.ext hxw)⟩

theorem gX_equivariant (γ : ↥K.fixingSubgroup) (x : repTorsionP p (XRep S K L hnorm)) :
    gXLin S K L hKL hL hnorm p hpS ((repTorsionP p (XRep S K L hnorm)).ρ γ x) = (sClassTorsionP K L hKL S p).ρ γ (gXLin S K L hKL hL hnorm p hpS x) := by

  obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (fX S L hL p hpS x.1)
  obtain ⟨C, rfl⟩ := Additive.ofMul.surjective a

  obtain ⟨hc, hx⟩ := repr_spec S L x.1
  set c := repr S L x.1
  have hx1 : x.1 = ⟨(H1π _).hom c, H1π_mem_continuousH1Sr _ S _ hc⟩ := Subtype.ext hx.symm

  have hρ : ((repTorsionP p (XRep S K L hnorm)).ρ γ x).1 = ⟨(H1π _).hom (conjCocycle₁ S (normalizes_of_mem K L hnorm γ) c),
      H1π_mem_continuousH1Sr _ S _ (isLevelConstantSr₁_conjCocycle₁ S _ hc)⟩ := by
    change (XRep S K L hnorm).ρ γ x.1 = _
    rw [hx1]
    exact Subtype.ext (conjX_mk S K L hnorm γ c hc)

  have hnat := (Classical.choose_spec (NumberField.LevelArith.exists_continuousH1Sr_sUnitsMaxRep_linearMap_sClassGroupRep_injective_natural S hpS L hL (p := p))).2.2
    (γ : Γ) (τ K L hKL γ) (hστ K L hKL γ) ⟨c, hc⟩ ⟨conjCocycle₁ S (normalizes_of_mem K L hnorm γ) c, isLevelConstantSr₁_conjCocycle₁ S _ hc⟩
    (block₁_conjCocycle₁ S L _ c) C (by rw [← hx1]; exact ha.symm)

  have hpin := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (NumberField.LevelArith.exists_restrict_and_torsionBy_sClassGroupRep_linearEquiv_sClassTorsionP S K L hKL hnorm (p := p))))
    γ ⟨fX S L hL p hpS x.1, fX_mem_torsion S L hL p hpS x⟩
      ⟨fX S L hL p hpS ((repTorsionP p (XRep S K L hnorm)).ρ γ x).1, fX_mem_torsion S L hL p hpS _⟩ C ha.symm (by
        change fX S L hL p hpS ((repTorsionP p (XRep S K L hnorm)).ρ γ x).1 =
          Submodule.Quotient.mk (Additive.ofMul (classGroupAut ℚ ↥L (τ' S K L hKL hnorm p γ) C))
        rw [hρ, τ'_eq_τ]
        exact hnat)
  exact hpin

def xClIso : repTorsionP p (XRep S K L hnorm) ≅ sClassTorsionP K L hKL S p :=
  Rep.mkIso (Representation.Equiv.mk (LinearEquiv.ofBijective (gXLin S K L hKL hL hnorm p hpS) (gX_bijective S K L hKL hL hnorm p hpS))
    fun γ => LinearMap.ext fun x => gX_equivariant S K L hKL hL hnorm p hpS γ x)

end NumberField.LevelArith.EQBK
p2m_reactivate "P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith.EQBK"
p2m_reactivate "P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith.EQBK"
p2m_reactivate "P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith.EQBK"

end
p2m_reactivate "P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith.EQBK"

noncomputable section
section PLISO_e6
p2m_open "CategoryTheory CategoryTheory.Limits NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith IsDedekindDomain P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.IsDedekindDomain NumberField~mem_placesOverPrimes_iff~placesOverPrimes P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField ExtCitation"
p2m_open_scoped "NumberField P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith Pointwise"
local notation "Γ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

namespace RepPi

variable {k G : Type} [CommRing k] [Group G] {ι : Type} [Fintype ι] [DecidableEq ι] (F : ι → Rep.{0} k G)

noncomputable def piρ : Representation k G (∀ i, F i) where
  toFun g := LinearMap.pi fun i => (F i).ρ g ∘ₗ LinearMap.proj i
  map_one' := by apply LinearMap.ext; intro f; funext i; simp
  map_mul' g h := by apply LinearMap.ext; intro f; funext i; simp

noncomputable def piObj : Rep.{0} k G := Rep.of (piρ F)

lemma piObj_ρ_apply (g : G) (f : ∀ i, F i) (i : ι) : (piObj F).ρ g f i = (F i).ρ g (f i) := rfl

private noncomputable def _root_.RepPi.proj (i : ι) : piObj F ⟶ F i :=
  Rep.ofHom ⟨LinearMap.proj i, fun _ => rfl⟩

p2m_export "RepPi" "proj"
lemma proj_hom_apply (i : ι) (f : ∀ i, F i) : (proj F i).hom f = f i := rfl

noncomputable def cmp : piObj F ⟶ ∏ᶜ F := Pi.lift (proj F)

lemma cmp_π (i : ι) : cmp F ≫ Pi.π F i = proj F i := Pi.lift_π _ _

lemma lift_forget_proj_comp_piIsoPi_hom :
    Pi.lift (fun j => (forget₂ (Rep.{0} k G) (ModuleCat.{0} k)).map (proj F j)) ≫ (ModuleCat.piIsoPi (fun j => (forget₂ (Rep.{0} k G) (ModuleCat.{0} k)).obj (F j))).hom = 𝟙 _ := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext; intro x
  funext i
  have h := congrArg (fun φ => (ModuleCat.Hom.hom φ) x)
    (show (Pi.lift (fun j => (forget₂ (Rep.{0} k G) (ModuleCat.{0} k)).map (proj F j)) ≫ (ModuleCat.piIsoPi (fun j => (forget₂ (Rep.{0} k G) (ModuleCat.{0} k)).obj (F j))).hom) ≫
        ModuleCat.ofHom (LinearMap.proj i) = (forget₂ (Rep.{0} k G) (ModuleCat.{0} k)).map (proj F i) by
      rw [Category.assoc, ModuleCat.piIsoPi_hom_ker_subtype, Pi.lift_π])
  exact h

scoped instance isIso_cmp : IsIso (cmp F) := by
  have h1 := map_lift_piComparison (forget₂ (Rep.{0} k G) (ModuleCat.{0} k)) F (piObj F) (proj F)
  have hL : Pi.lift (fun j => (forget₂ (Rep.{0} k G) (ModuleCat.{0} k)).map (proj F j)) = (ModuleCat.piIsoPi (fun j => (forget₂ (Rep.{0} k G) (ModuleCat.{0} k)).obj (F j))).inv :=
    (Iso.comp_hom_eq_id _).1 (lift_forget_proj_comp_piIsoPi_hom F)
  have h2 : (forget₂ (Rep.{0} k G) (ModuleCat.{0} k)).map (cmp F) = Pi.lift (fun j => (forget₂ (Rep.{0} k G) (ModuleCat.{0} k)).map (proj F j)) ≫ inv (piComparison (forget₂ (Rep.{0} k G) (ModuleCat.{0} k)) F) :=
    (IsIso.eq_comp_inv _).2 h1
  haveI : IsIso ((forget₂ (Rep.{0} k G) (ModuleCat.{0} k)).map (cmp F)) := by rw [h2, hL]; infer_instance
  exact isIso_of_reflects_iso (cmp F) (forget₂ (Rep.{0} k G) (ModuleCat.{0} k))

end RepPi
p2m_reactivate "P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith.EQBK P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.RepPi"

namespace PlIsoWork

local notation "Qbar" => (AlgebraicClosure ℚ)

variable (S : Finset Nat.Primes) (K L : IntermediateField ℚ Qbar) (hKL : K ≤ L)
  [FiniteDimensional ℚ ↥K] [FiniteDimensional ℚ ↥L] [Normal ↥K ↥(levelField K L hKL)] (hnorm : IsNormalLevel K L)

noncomputable def eO : 𝓞 ↥L ≃+* 𝓞 ↥(levelField K L hKL) := NumberField.RingOfIntegers.mapRingEquiv (levelFieldEquiv K L hKL)

lemma coe_eO (y : 𝓞 ↥L) : (((eO K L hKL y : 𝓞 ↥(levelField K L hKL)) : ↥(levelField K L hKL)) : Qbar) = ((y : ↥L) : Qbar) := rfl

noncomputable def placeEquiv : HeightOneSpectrum (𝓞 ↥L) ≃ HeightOneSpectrum (𝓞 ↥(levelField K L hKL)) :=
  HeightOneSpectrum.equivOfRingEquiv (eO K L hKL)

lemma mem_placeEquiv_symm_asIdeal_iff (w' : HeightOneSpectrum (𝓞 ↥(levelField K L hKL))) (r : 𝓞 ↥L) :
    r ∈ ((placeEquiv K L hKL).symm w').asIdeal ↔ eO K L hKL r ∈ w'.asIdeal := Iff.rfl

lemma placeEquiv_symm_asIdeal (w' : HeightOneSpectrum (𝓞 ↥(levelField K L hKL))) :
    ((placeEquiv K L hKL).symm w').asIdeal = w'.asIdeal.comap (eO K L hKL : 𝓞 ↥L →+* 𝓞 ↥(levelField K L hKL)) := rfl

lemma ringOfIntegersAut_comm (γ : ↥K.fixingSubgroup) :
    (ringOfIntegersAut ℚ ↥L (NumberField.LevelArith.EQBK.τ K L hKL γ)).trans (eO K L hKL) =
      (eO K L hKL).trans (ringOfIntegersAut ↥K ↥(levelField K L hKL) (levelGal K L hKL γ)) := by
  apply RingEquiv.ext; intro y
  apply Subtype.ext; apply Subtype.ext
  show ((NumberField.LevelArith.EQBK.τ K L hKL γ (y : ↥L) : ↥L) : Qbar) =
    (((levelGal K L hKL γ) ((eO K L hKL y : 𝓞 ↥(levelField K L hKL)) : ↥(levelField K L hKL))) : Qbar)
  rw [levelGal_apply_coe, coe_eO, NumberField.LevelArith.EQBK.coe_τ]

lemma ringOfIntegersAut_inv (γ : ↥K.fixingSubgroup) :
    ringOfIntegersAut ↥K ↥(levelField K L hKL) (levelGal K L hKL γ⁻¹) =
      (ringOfIntegersAut ↥K ↥(levelField K L hKL) (levelGal K L hKL γ)).symm := by
  apply RingEquiv.ext; intro y
  rw [map_inv]
  rfl

noncomputable def pl (q : ↥S) (e : placesAbove L S (Sum.inr q) ≃
      {w : HeightOneSpectrum (𝓞 ↥(levelField K L hKL)) // ((((q : Nat.Primes) : ℕ) : 𝓞 ↥(levelField K L hKL)) ∈ w.asIdeal)})
    (x : placesAbove L S (Sum.inr q)) : ↥(placesOverPrimes ↥L (S : Set Nat.Primes)) :=
  ⟨(placeEquiv K L hKL).symm (e x).1, by
    rw [mem_placesOverPrimes_iff]
    refine ⟨q, q.2, ?_⟩
    rw [mem_placeEquiv_symm_asIdeal_iff, map_natCast]
    exact (e x).2⟩

omit [FiniteDimensional ℚ ↥K] [Normal ↥K ↥(levelField K L hKL)] in

lemma natCast_mem_unique {q q' : ℕ} (hq : q.Prime) (hq' : q'.Prime) (w : HeightOneSpectrum (𝓞 ↥L))
    (h : ((q : 𝓞 ↥L)) ∈ w.asIdeal) (h' : ((q' : 𝓞 ↥L)) ∈ w.asIdeal) : q = q' := by
  by_contra hne
  have hcop : IsCoprime ((q : 𝓞 ↥L)) ((q' : 𝓞 ↥L)) := by
    have := (Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hq hq').2 hne)).map (Int.castRingHom (𝓞 ↥L))
    simpa using this
  obtain ⟨a, b, hab⟩ := hcop
  apply w.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← hab]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h) (Ideal.mul_mem_left _ _ h')

lemma sigmaPl_bijective (e : ∀ q : ↥S, placesAbove L S (Sum.inr q) ≃
      {w : HeightOneSpectrum (𝓞 ↥(levelField K L hKL)) // ((((q : Nat.Primes) : ℕ) : 𝓞 ↥(levelField K L hKL)) ∈ w.asIdeal)}) :
    Function.Bijective (fun qx : Σ q : ↥S, placesAbove L S (Sum.inr q) => pl S K L hKL qx.1 (e qx.1) qx.2) := by
  constructor
  · rintro ⟨q, x⟩ ⟨q', x'⟩ h
    have hw : (placeEquiv K L hKL).symm (e q x).1 = (placeEquiv K L hKL).symm (e q' x').1 := congrArg Subtype.val h
    have hw' : (e q x).1 = (e q' x').1 := (placeEquiv K L hKL).symm.injective hw
    have hqq : q = q' := by
      apply Subtype.ext; apply Subtype.ext
      have h1 : ((((q : Nat.Primes) : ℕ) : 𝓞 ↥L)) ∈ ((placeEquiv K L hKL).symm (e q x).1).asIdeal := by
        rw [mem_placeEquiv_symm_asIdeal_iff, map_natCast]; exact (e q x).2
      have h2 : ((((q' : Nat.Primes) : ℕ) : 𝓞 ↥L)) ∈ ((placeEquiv K L hKL).symm (e q x).1).asIdeal := by
        rw [hw, mem_placeEquiv_symm_asIdeal_iff, map_natCast]; exact (e q' x').2
      exact natCast_mem_unique L (q : Nat.Primes).2 (q' : Nat.Primes).2 _ h1 h2
    subst hqq
    have hx : x = x' := (e q).injective (Subtype.ext hw')
    subst hx
    rfl
  · rintro ⟨w, hw⟩
    obtain ⟨q, hq, hqw⟩ := (mem_placesOverPrimes_iff _ _ _).1 hw
    have hq' : ((((q : Nat.Primes) : ℕ) : 𝓞 ↥(levelField K L hKL))) ∈ (placeEquiv K L hKL w).asIdeal := by
      show (eO K L hKL).symm _ ∈ w.asIdeal
      rw [map_natCast]; exact hqw
    refine ⟨⟨⟨q, hq⟩, (e ⟨q, hq⟩).symm ⟨placeEquiv K L hKL w, hq'⟩⟩, Subtype.ext ?_⟩
    show (placeEquiv K L hKL).symm (e ⟨q, hq⟩ ((e ⟨q, hq⟩).symm ⟨placeEquiv K L hKL w, hq'⟩)).1 = w
    rw [Equiv.apply_symm_apply, Equiv.symm_apply_apply]

noncomputable def σ (e : ∀ q : ↥S, placesAbove L S (Sum.inr q) ≃
      {w : HeightOneSpectrum (𝓞 ↥(levelField K L hKL)) // ((((q : Nat.Primes) : ℕ) : 𝓞 ↥(levelField K L hKL)) ∈ w.asIdeal)}) :
    (Σ q : ↥S, placesAbove L S (Sum.inr q)) ≃ ↥(placesOverPrimes ↥L (S : Set Nat.Primes)) :=
  Equiv.ofBijective _ (sigmaPl_bijective S K L hKL e)

lemma σ_apply (e : ∀ q : ↥S, placesAbove L S (Sum.inr q) ≃
      {w : HeightOneSpectrum (𝓞 ↥(levelField K L hKL)) // ((((q : Nat.Primes) : ℕ) : 𝓞 ↥(levelField K L hKL)) ∈ w.asIdeal)})
    (q : ↥S) (x : placesAbove L S (Sum.inr q)) : σ S K L hKL e ⟨q, x⟩ = pl S K L hKL q (e q) x := rfl

end PlIsoWork
p2m_reactivate "P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith.EQBK P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.RepPi"

namespace PlIsoWork

local notation "Qbar" => (AlgebraicClosure ℚ)

variable (S : Finset Nat.Primes) (K L : IntermediateField ℚ Qbar) (hKL : K ≤ L)
  [FiniteDimensional ℚ ↥K] [FiniteDimensional ℚ ↥L] [Normal ↥K ↥(levelField K L hKL)] (hnorm : IsNormalLevel K L)
  (p : ℕ) [Fact p.Prime]

def sigmaCurry (A : ↥S → Type) : ((Σ q : ↥S, A q) → ZMod p) ≃ₗ[ZMod p] (∀ q : ↥S, A q → ZMod p) :=
  { Equiv.piCurry (fun (_ : ↥S) (_ : A _) => ZMod p) with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

variable (e : ∀ q : ↥S, placesAbove L S (Sum.inr q) ≃
      {w : HeightOneSpectrum (𝓞 ↥(levelField K L hKL)) // ((((q : Nat.Primes) : ℕ) : 𝓞 ↥(levelField K L hKL)) ∈ w.asIdeal)})

scoped instance finite_primesOver (q : ↥S) :
    Finite {w : HeightOneSpectrum (𝓞 ↥(levelField K L hKL)) // ((((q : Nat.Primes) : ℕ) : 𝓞 ↥(levelField K L hKL)) ∈ w.asIdeal)} := by
  have hI : (Ideal.span {((((q : Nat.Primes) : ℕ) : 𝓞 ↥(levelField K L hKL)))} : Ideal (𝓞 ↥(levelField K L hKL))) ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact Nat.cast_ne_zero.2 (q : Nat.Primes).2.ne_zero
  have := Ideal.finite_factors hI
  refine Set.Finite.to_subtype (this.subset fun w hw => ?_)
  show w.asIdeal ∣ Ideal.span _
  rw [Ideal.dvd_span_singleton]
  exact hw

variable [hfin : ∀ q : ↥S, Finite (placesAbove L S (Sum.inr q))]

noncomputable def Ξ : (↥(placesOverPrimes ↥L (S : Set Nat.Primes)) → ZMod p) ≃ₗ[ZMod p]
    (∀ q : ↥S, (placesAbove L S (Sum.inr q) →₀ ZMod p)) :=
  (LinearEquiv.funCongrLeft (ZMod p) (ZMod p) (σ S K L hKL e)).trans
    ((sigmaCurry S p (fun q => placesAbove L S (Sum.inr q))).trans
      (LinearEquiv.piCongrRight fun q => (Finsupp.linearEquivFunOnFinite (ZMod p) (ZMod p) (placesAbove L S (Sum.inr q))).symm))

lemma Ξ_apply (f : ↥(placesOverPrimes ↥L (S : Set Nat.Primes)) → ZMod p) (q : ↥S) (x : placesAbove L S (Sum.inr q)) :
    Ξ S K L hKL p e f q x = f (pl S K L hKL q (e q) x) := by
  simp only [Ξ, LinearEquiv.trans_apply, LinearEquiv.piCongrRight_apply, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply,
    Finsupp.linearEquivFunOnFinite_symm_coe]
  rfl

include hnorm in

lemma placePull_pl (he : ∀ (q : ↥S) (γ : ↥K.fixingSubgroup) (x : placesAbove L S (Sum.inr q)),
      ((e q ((orbitQuotientAction K L hnorm (Γ ⧸ (extArithLoc S (Sum.inr q)).range)).smul γ x)).1).asIdeal =
        ((e q x).1).asIdeal.map (ringOfIntegersAut ↥K ↥(levelField K L hKL) (levelGal K L hKL γ)))
    (γ : ↥K.fixingSubgroup) (q : ↥S) (x : placesAbove L S (Sum.inr q)) :
    NumberField.LevelArith.EQBK.placePull S K L hKL γ (pl S K L hKL q (e q) x) =
      pl S K L hKL q (e q) ((orbitQuotientAction K L hnorm (Γ ⧸ (extArithLoc S (Sum.inr q)).range)).smul γ⁻¹ x) := by
  apply Subtype.ext
  apply HeightOneSpectrum.ext
  show (((e q x).1.asIdeal.comap (eO K L hKL : 𝓞 ↥L →+* 𝓞 ↥(levelField K L hKL))).comap
      (ringOfIntegersAut ℚ ↥L (NumberField.LevelArith.EQBK.τ K L hKL γ) : 𝓞 ↥L →+* 𝓞 ↥L)) =
    ((e q ((orbitQuotientAction K L hnorm (Γ ⧸ (extArithLoc S (Sum.inr q)).range)).smul γ⁻¹ x)).1.asIdeal).comap
      (eO K L hKL : 𝓞 ↥L →+* 𝓞 ↥(levelField K L hKL))
  rw [he q γ⁻¹ x, ringOfIntegersAut_inv, Ideal.comap_comap,
    show (eO K L hKL : 𝓞 ↥L →+* 𝓞 ↥(levelField K L hKL)).comp (ringOfIntegersAut ℚ ↥L (NumberField.LevelArith.EQBK.τ K L hKL γ) : 𝓞 ↥L →+* 𝓞 ↥L) =
      (((ringOfIntegersAut ℚ ↥L (NumberField.LevelArith.EQBK.τ K L hKL γ)).trans (eO K L hKL) : 𝓞 ↥L ≃+* 𝓞 ↥(levelField K L hKL)) :
        𝓞 ↥L →+* 𝓞 ↥(levelField K L hKL)) from rfl,
    ringOfIntegersAut_comm,
    show (((eO K L hKL).trans (ringOfIntegersAut ↥K ↥(levelField K L hKL) (levelGal K L hKL γ)) : 𝓞 ↥L ≃+* 𝓞 ↥(levelField K L hKL)) :
        𝓞 ↥L →+* 𝓞 ↥(levelField K L hKL)) =
      (ringOfIntegersAut ↥K ↥(levelField K L hKL) (levelGal K L hKL γ) : 𝓞 ↥(levelField K L hKL) →+* 𝓞 ↥(levelField K L hKL)).comp
        (eO K L hKL : 𝓞 ↥L →+* 𝓞 ↥(levelField K L hKL)) from rfl,
    ← Ideal.comap_comap]
  congr 1
  rw [Ideal.map_symm]
  rfl

end PlIsoWork
p2m_reactivate "P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith.EQBK P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.RepPi P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.PlIsoWork"

namespace PlIsoWork

local notation "Qbar" => (AlgebraicClosure ℚ)

variable (S : Finset Nat.Primes) (K L : IntermediateField ℚ Qbar) (hKL : K ≤ L)
  [FiniteDimensional ℚ ↥K] [FiniteDimensional ℚ ↥L] [Normal ↥K ↥(levelField K L hKL)] (hnorm : IsNormalLevel K L)
  (p : ℕ) [Fact p.Prime] [hfin : ∀ q : ↥S, Finite (placesAbove L S (Sum.inr q))]
  (e : ∀ q : ↥S, placesAbove L S (Sum.inr q) ≃
      {w : HeightOneSpectrum (𝓞 ↥(levelField K L hKL)) // ((((q : Nat.Primes) : ℕ) : 𝓞 ↥(levelField K L hKL)) ∈ w.asIdeal)})
  (he : ∀ (q : ↥S) (γ : ↥K.fixingSubgroup) (x : placesAbove L S (Sum.inr q)),
      ((e q ((orbitQuotientAction K L hnorm (Γ ⧸ (extArithLoc S (Sum.inr q)).range)).smul γ x)).1).asIdeal =
        ((e q x).1).asIdeal.map (ringOfIntegersAut ↥K ↥(levelField K L hKL) (levelGal K L hKL γ)))

include he in
lemma Ξ_equivariant (γ : ↥K.fixingSubgroup) (f : ↥(placesOverPrimes ↥L (S : Set Nat.Primes)) → ZMod p) :
    Ξ S K L hKL p e ((NumberField.LevelArith.EQBK.PlRep S K L hKL p).ρ γ f) =
      (RepPi.piObj (fun q : ↥S => placesRep K L hnorm S (Sum.inr q) p)).ρ γ (Ξ S K L hKL p e f) := by
  funext q
  letI : MulAction ↥K.fixingSubgroup (placesAbove L S (Sum.inr q)) :=
    orbitQuotientAction K L hnorm (Γ ⧸ (extArithLoc S (Sum.inr q)).range)
  show (Ξ S K L hKL p e ((NumberField.LevelArith.EQBK.PlRep S K L hKL p).ρ γ f) q : placesAbove L S (Sum.inr q) →₀ ZMod p) =
    Finsupp.lmapDomain (ZMod p) (ZMod p) (γ • ·) (Ξ S K L hKL p e f q)
  apply Finsupp.ext; intro x
  rw [Ξ_apply, NumberField.LevelArith.EQBK.PlRep_ρ_apply, placePull_pl S K L hKL hnorm e he, Finsupp.lmapDomain_apply]
  conv_rhs => rw [← smul_inv_smul γ x]
  rw [Finsupp.mapDomain_apply (MulAction.injective γ), Ξ_apply]
  rfl

noncomputable def isoPi : NumberField.LevelArith.EQBK.PlRep S K L hKL p ≅ RepPi.piObj (fun q : ↥S => placesRep K L hnorm S (Sum.inr q) p) :=
  Rep.mkIso (Representation.Equiv.mk (Ξ S K L hKL p e) fun γ => LinearMap.ext (Ξ_equivariant S K L hKL hnorm p e he γ))

noncomputable def PlIso : NumberField.LevelArith.EQBK.PlRep S K L hKL p ≅ ∏ᶜ fun q : ↥S => placesRep K L hnorm S (Sum.inr q) p :=
  isoPi S K L hKL hnorm p e he ≪≫ asIso (RepPi.cmp (fun q : ↥S => placesRep K L hnorm S (Sum.inr q) p))

end PlIsoWork
p2m_reactivate "P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith.EQBK P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.RepPi P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.PlIsoWork"

namespace NumberField
p2m_export "NumberField" "mk place RingOfIntegers RingOfIntegers.mapRingEquiv LevelArith.exists_continuousH1Sr_sUnitsMaxRep_linearMap_sClassGroupRep_injective_natural LevelArith.exists_continuousH1Sr_sUnitsMaxRep_linearMap_sClassGroupRep_injective LevelArith.exists_restrict_and_torsionBy_sClassGroupRep_linearEquiv_sClassTorsionP LevelArith.exists_placesAbove_inr_equiv_primesOver LevelArith.nonempty_repTorsionP_iso_repModP"
namespace LevelArith
p2m_export "NumberField.LevelArith" "levelField LevelGal levelFieldEquiv coe_levelFieldEquiv coe_levelFieldEquiv_symm levelGal levelGal_apply_coe modP modP_apply_mk repModP repTorsionP ringOfIntegersAut classGroupAut classGroupRep placesOverPrimes mem_placesOverPrimes_iff placesOverPrimes_finite sClassGroupRep sClassTorsionP IsNormalLevel orbitQuotientAction placesAbove placesRep sUnitsMax sUnitsMaxStable mem_sUnitsMaxStable_iff sUnitsMaxStable_le sUnitsMaxRep sUnitsMaxRep.val exists_continuousH1Sr_sUnitsMaxRep_linearMap_sClassGroupRep_injective_natural exists_continuousH1Sr_sUnitsMaxRep_linearMap_sClassGroupRep_injective exists_restrict_and_torsionBy_sClassGroupRep_linearEquiv_sClassTorsionP exists_placesAbove_inr_equiv_primesOver nonempty_repTorsionP_iso_repModP sUnitsMaxStable_eq_sUnitsMax"
namespace EQBK
p2m_open "NumberField.LevelArith NumberField~mem_placesOverPrimes_iff~placesOverPrimes"

noncomputable def plIso (S : Finset Nat.Primes) (K L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hKL : K ≤ L)
    [FiniteDimensional ℚ ↥K] [FiniteDimensional ℚ ↥L] [Normal ↥K ↥(levelField K L hKL)] (hnorm : IsNormalLevel K L)
    (p : ℕ) [Fact p.Prime] :
    PlRep S K L hKL p ≅ ∏ᶜ fun q : ↥S => placesRep K L hnorm S (Sum.inr q) p := by
  let e := fun q : ↥S => Classical.choose (NumberField.LevelArith.exists_placesAbove_inr_equiv_primesOver K L hKL hnorm S q)
  have he := fun q : ↥S => Classical.choose_spec (NumberField.LevelArith.exists_placesAbove_inr_equiv_primesOver K L hKL hnorm S q)
  haveI : ∀ q : ↥S, Finite (placesAbove L S (Sum.inr q)) := fun q => Finite.of_equiv _ (e q).symm
  exact PlIsoWork.PlIso S K L hKL hnorm p e he

end NumberField.LevelArith.EQBK
p2m_reactivate "P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith.EQBK P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.RepPi P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.PlIsoWork"
p2m_reactivate "P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith.EQBK P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.RepPi P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.PlIsoWork"
p2m_reactivate "P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith.EQBK P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.RepPi P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.PlIsoWork"

end PLISO_e6
p2m_reactivate "P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith.EQBK P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.RepPi P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.PlIsoWork"
end
p2m_reactivate "P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith.EQBK P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.RepPi P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.PlIsoWork"

noncomputable section
section XTORS_e6
p2m_open "CategoryTheory Module NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith ExtCitation"
p2m_open_scoped "NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith Pointwise"

namespace XTors

section Descent
variable {k : Type} [CommRing k] {G H : Type} [Group G] [Group H] (φ : G →* H) (hφ : Function.Surjective φ)
  (N : Rep.{0} k G) (hker : ∀ g : G, φ g = 1 → N.ρ g = 1)

include hker in
lemma rho_eq_of_apply_eq {g g' : G} (h : φ g = φ g') : N.ρ g = N.ρ g' := by
  have : g = g' * (g'⁻¹ * g) := by group
  rw [this, map_mul, hker (g'⁻¹ * g) (by rw [map_mul, map_inv, h, inv_mul_cancel]), mul_one]

noncomputable def descentρ : Representation k H N where
  toFun h := N.ρ (Function.surjInv hφ h)
  map_one' := hker _ (Function.surjInv_eq hφ 1)
  map_mul' a b := by
    rw [← map_mul]
    apply rho_eq_of_apply_eq φ N hker
    rw [map_mul, Function.surjInv_eq hφ, Function.surjInv_eq hφ, Function.surjInv_eq hφ]

noncomputable def descent : Rep.{0} k H := Rep.of (descentρ φ hφ N hker)

lemma descent_ρ_apply (g : G) : (descent φ hφ N hker).ρ (φ g) = N.ρ g :=
  rho_eq_of_apply_eq φ N hker (Function.surjInv_eq hφ (φ g))

noncomputable def isoResDescent : N ≅ Rep.res φ (descent φ hφ N hker) :=
  Rep.mkIso (Representation.Equiv.mk (LinearEquiv.refl k N) fun g => by
    apply LinearMap.ext; intro v
    show N.ρ g v = (descent φ hφ N hker).ρ (φ g) v
    exact congrFun (congrArg DFunLike.coe (descent_ρ_apply φ hφ N hker g).symm) v)

end Descent
p2m_reactivate "P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith.EQBK P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.RepPi P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.PlIsoWork"

section Main
variable {Γ : Type} [Group Γ] (Λ : Subgroup Γ) [Λ.Normal] (p : ℕ) [Fact p.Prime] (A : Rep.{0} ℤ Γ)
  (hΛ : ∀ s ∈ Λ, A.ρ s = 1)

private abbrev _root_.XTors.π : Γ →* Γ ⧸ Λ := QuotientGroup.mk' Λ

p2m_export "XTors" "π"
lemma π_surjective : Function.Surjective (π Λ) := QuotientGroup.mk'_surjective Λ

include hΛ in
lemma hker : ∀ g : Γ, π Λ g = 1 → A.ρ g = 1 := fun g hg => hΛ g ((QuotientGroup.eq_one_iff g).1 hg)

noncomputable abbrev Abar : Rep.{0} ℤ (Γ ⧸ Λ) := descent (π Λ) (π_surjective Λ) A (hker Λ A hΛ)

lemma Abar_ρ_apply (g : Γ) : (Abar Λ A hΛ).ρ (π Λ g) = A.ρ g := descent_ρ_apply (π Λ) (π_surjective Λ) A (hker Λ A hΛ) g

scoped instance [Finite A] : Finite (Abar Λ A hΛ) := inferInstanceAs (Finite A)

noncomputable def isoOfEq {k G : Type} [CommRing k] [Group G] {V : Type} [AddCommGroup V] [Module k V]
    (ρ σ : Representation k G V) (h : ∀ g, ρ g = σ g) : Rep.of ρ ≅ Rep.of σ :=
  Rep.mkIso (Representation.Equiv.mk (LinearEquiv.refl k V) fun g => by rw [h g]; rfl)

noncomputable def torsionIso : repTorsionP p A ≅ Rep.res (π Λ) (repTorsionP p (Abar Λ A hΛ)) :=
  isoOfEq (repTorsionP p A).ρ (Rep.res (π Λ) (repTorsionP p (Abar Λ A hΛ))).ρ fun g =>
    LinearMap.ext fun x => Subtype.ext ((DFunLike.congr_fun (Abar_ρ_apply Λ A hΛ g) x.1).symm)

noncomputable def modPIso : repModP p A ≅ Rep.res (π Λ) (repModP p (Abar Λ A hΛ)) :=
  isoOfEq (repModP p A).ρ (Rep.res (π Λ) (repModP p (Abar Λ A hΛ))).ρ fun g =>
    LinearMap.ext fun x => by
      induction x using Submodule.Quotient.induction_on with
      | H a =>
        show modP p A.ρ g _ = modP p (Abar Λ A hΛ).ρ (π Λ g) _
        rw [modP_apply_mk]
        erw [modP_apply_mk]
        rw [Abar_ρ_apply]
        rfl

include hΛ in

theorem nonempty_repModP_iso_repTorsionP_of_trivial [Finite (Γ ⧸ Λ)] (hcop : (Nat.card (Γ ⧸ Λ)).Coprime p) [Finite A] :
    Nonempty (repModP p A ≅ repTorsionP p A) := by
  obtain ⟨eT⟩ := NumberField.LevelArith.nonempty_repTorsionP_iso_repModP p hcop (Abar Λ A hΛ)
  exact ⟨modPIso Λ p A hΛ ≪≫ (Rep.resFunctor (π Λ)).mapIso eT.symm ≪≫ (torsionIso Λ p A hΛ).symm⟩

end Main
p2m_reactivate "P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith.EQBK P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.RepPi P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.PlIsoWork"

end XTors
p2m_reactivate "P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith.EQBK P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.RepPi P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.PlIsoWork P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.XTors"

end XTORS_e6
p2m_reactivate "P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith.EQBK P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.RepPi P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.PlIsoWork P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.XTors"
end
p2m_reactivate "P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith.EQBK P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.RepPi P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.PlIsoWork P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.XTors"

noncomputable section

namespace NumberField
p2m_export "NumberField" "mk place RingOfIntegers RingOfIntegers.mapRingEquiv LevelArith.exists_continuousH1Sr_sUnitsMaxRep_linearMap_sClassGroupRep_injective_natural LevelArith.exists_continuousH1Sr_sUnitsMaxRep_linearMap_sClassGroupRep_injective LevelArith.exists_restrict_and_torsionBy_sClassGroupRep_linearEquiv_sClassTorsionP LevelArith.exists_placesAbove_inr_equiv_primesOver LevelArith.nonempty_repTorsionP_iso_repModP"
namespace LevelArith
p2m_export "NumberField.LevelArith" "levelField LevelGal levelFieldEquiv coe_levelFieldEquiv coe_levelFieldEquiv_symm levelGal levelGal_apply_coe modP modP_apply_mk repModP repTorsionP ringOfIntegersAut classGroupAut classGroupRep placesOverPrimes mem_placesOverPrimes_iff placesOverPrimes_finite sClassGroupRep sClassTorsionP IsNormalLevel orbitQuotientAction placesAbove placesRep sUnitsMax sUnitsMaxStable mem_sUnitsMaxStable_iff sUnitsMaxStable_le sUnitsMaxRep sUnitsMaxRep.val exists_continuousH1Sr_sUnitsMaxRep_linearMap_sClassGroupRep_injective_natural exists_continuousH1Sr_sUnitsMaxRep_linearMap_sClassGroupRep_injective exists_restrict_and_torsionBy_sClassGroupRep_linearEquiv_sClassTorsionP exists_placesAbove_inr_equiv_primesOver nonempty_repTorsionP_iso_repModP sUnitsMaxStable_eq_sUnitsMax"
namespace EQBK
p2m_open "NumberField.LevelArith NumberField~mem_placesOverPrimes_iff~placesOverPrimes"

p2m_open "groupCohomology CategoryTheory IsDedekindDomain P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.IsDedekindDomain ExtCitation CategoryTheory.Limits CategoryTheory.MonoidalCategory.Limits"
p2m_open_scoped "NumberField P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith Pointwise"

theorem main
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (K L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hK : K.IsUnramifiedOutside S) (hL : L.IsUnramifiedOutside S)
    [FiniteDimensional ℚ ↥K] [FiniteDimensional ℚ ↥L]
    (hKL : K ≤ L) [Normal ↥K ↥(levelField K L hKL)] [(L.fixingSubgroup.subgroupOf K.fixingSubgroup).Normal]
    (hnorm : ∀ g ∈ K.fixingSubgroup, ∀ s ∈ L.fixingSubgroup, g * s * g⁻¹ ∈ L.fixingSubgroup)
    (hcop : (L.fixingSubgroup.relIndex K.fixingSubgroup).Coprime p)
    (h4 : p = 2 → ∃ i ∈ L, i ^ 2 = -1) :
    FiniteDimensional (ZMod p) (cyclotomicQuotientH2Rep S K L p) ∧
      Nonempty ((cyclotomicQuotientH2Rep S K L p ⊞ Rep.trivial (ZMod p) ↥K.fixingSubgroup (ZMod p) : Rep.{0} (ZMod p) ↥K.fixingSubgroup) ≅
        sClassTorsionP K L hKL S p ⊞ ∏ᶜ fun q : ↥S => placesRep K L hnorm S (Sum.inr q) p) := by

  haveI : (L.fixingSubgroup.subgroupOf K.fixingSubgroup).FiniteIndex := ⟨fun h0 => by
    have : L.fixingSubgroup.relIndex K.fixingSubgroup = 0 := h0
    rw [this, Nat.coprime_zero_left] at hcop
    exact (Fact.out : p.Prime).one_lt.ne' hcop⟩
  haveI : Finite ↥(X S L) := finite_X S L hL p hpS
  haveI : Finite (XRep S K L hnorm) := finite_X S L hL p hpS
  obtain ⟨e1⟩ := split₁ S K L hKL hL hnorm p hcop hpS h4
  obtain ⟨e2⟩ := split₂ S K L hKL hL hnorm p hcop hpS h4
  obtain ⟨e3⟩ := XTors.nonempty_repModP_iso_repTorsionP_of_trivial (L.fixingSubgroup.subgroupOf K.fixingSubgroup) p (XRep S K L hnorm)
    (fun s hs => XRep_ρ_eq_one_of_mem S K L hnorm s (Subgroup.mem_subgroupOf.1 hs)) (hcop' K L p hcop)
  refine ⟨fd_A₂ S K L hKL hL p hpS h4, ⟨?_⟩⟩
  exact biprod.mapIso (ΘIso S K L hKL hL p ≪≫ e1) (Iso.refl _) ≪≫ biprod.associator _ _ _ ≪≫
    biprod.mapIso (Iso.refl _) e2.symm ≪≫ biprod.mapIso (e3 ≪≫ xClIso S K L hKL hL hnorm p hpS) (plIso S K L hKL hnorm p)

end NumberField.LevelArith.EQBK
p2m_reactivate "P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith.EQBK P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.RepPi P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.PlIsoWork P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.XTors"
p2m_reactivate "P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith.EQBK P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.RepPi P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.PlIsoWork P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.XTors"
p2m_reactivate "P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith.EQBK P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.RepPi P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.PlIsoWork P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.XTors"

end
p2m_reactivate "P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.NumberField.LevelArith.EQBK P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.RepPi P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.PlIsoWork P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.XTors"

theorem solution
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (K L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hK : K.IsUnramifiedOutside S) (hL : L.IsUnramifiedOutside S)
    [FiniteDimensional ℚ ↥K] [FiniteDimensional ℚ ↥L]
    (hKL : K ≤ L) [Normal ↥K ↥(levelField K L hKL)] [(L.fixingSubgroup.subgroupOf K.fixingSubgroup).Normal]
    (hnorm : ∀ g ∈ K.fixingSubgroup, ∀ s ∈ L.fixingSubgroup, g * s * g⁻¹ ∈ L.fixingSubgroup)
    (hcop : (L.fixingSubgroup.relIndex K.fixingSubgroup).Coprime p)
    (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p) (hζL : ζ ∈ L)
    (h4 : p = 2 → ∃ i ∈ L, i ^ 2 = -1) :
    FiniteDimensional (ZMod p) (cyclotomicQuotientH2Rep S K L p) ∧
      Nonempty ((cyclotomicQuotientH2Rep S K L p ⊞ Rep.trivial (ZMod p) ↥K.fixingSubgroup (ZMod p) : Rep.{0} (ZMod p) ↥K.fixingSubgroup) ≅
        sClassTorsionP K L hKL S p ⊞ ∏ᶜ fun q : ↥S => placesRep K L hnorm S (Sum.inr q) p) := by
  exact NumberField.LevelArith.EQBK.main S hpS K L hK hL hKL hnorm hcop h4

end S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso
end P2MW
export P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso (solution)
