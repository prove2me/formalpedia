-- Prove2me | solution 1 for groupCohomology.greenbergWilesLeAdm_extArithLoc_of_isTheta1_eval_of_ne_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/5d51e312-0dd6-5615-ba7a-7bfb4e416778

import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GroupCohomology_Selmer
import Definitions.Def_GroupCohomology_SelmerAdm
import Definitions.Def_GroupCohomology_ContinuousDuality
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_GroupCohomology_LocalInvariant
import Theorems.Thm_groupCohomology_eq_continuousH1S_of_forall_mem_iff
import Theorems.Thm_groupCohomology_finiteDimensional_continuousH1S
import Theorems.Thm_groupCohomology_exists_mem_continuousH1S_locRes_eq_iff_forall_sum_theta_eq_zero_of_ne_two
import Theorems.Thm_groupCohomology_isLocalInv_localInv_and_bijective
import Theorems.Thm_groupCohomology_finiteDimensional_continuousH1_of_isOpen_of_primeLocal
import Theorems.Thm_groupCohomology_map_apply_mem_continuousH1_comp
import Theorems.Thm_groupCohomology_finrank_finiteQuotientH1_eq_invariants_add_dualTwist_add_finrank_of_primeLocal
import Theorems.Thm_groupCohomology_finrank_finiteQuotientH1_eq_invariants_add_dualTwist_of_primeLocal_ne
import Theorems.Thm_groupCohomology_finrank_invariants_add_finrank_continuousH2S_add_finrank_eq_of_ne_two
import Theorems.Thm_groupCohomology_finrank_sha1_dualTwist_eq_finrank_sha2_of_ne_two
import Theorems.Thm_groupCohomology_exists_continuousH2S_locRes_eq_iff_and_surjective_sum_theta2_of_ne_two
import Theorems.Thm_groupCohomology_exists_theta0_and_theta2
import Theorems.Thm_groupCohomology_exists_theta1
import Theorems.Thm_groupCohomology_bijective_theta_dualTwist_of_primeLocal
import Theorems.Thm_groupCohomology_locRes_extArithLoc_apply_mem_continuousH1
import Theorems.Thm_Rep_isEquivariantBilinear_eval_dualTwist
import Theorems.Thm_Rep_dualTwist_smooth
import Theorems.Thm_groupCohomology_exists_level_ofChar_cycloChar_comp
import Theorems.Thm_TWNum_finiteDimensional_continuousH2S
import Theorems.Thm_TWNum_subsingleton_continuousH2_extArithLoc_inl
import Theorems.Thm_TWNum_subsingleton_H1_extArithLoc_inl_dualTwist
import Theorems.Thm_ValuationSubring_apply_eq_self_of_pow_eq_one_of_mem_inertiaSubgroupIn
import Theorems.Thm_Submodule_finrank_comap_eq_finrank_ker_add_finrank_range_inf
import Theorems.Thm_Submodule_finrank_pi_univ_eq_sum
import Theorems.Thm_groupCohomology_injective_H1_restriction_of_isUnit_index
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_greenbergWilesLeAdm_extArithLoc_of_isTheta1_eval_of_ne_two
p2m_attr_erase "instance" "M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion NumberField.AdelicHaar.locallyCompactSpace_adeleRing NumberField.AdelicHaar.finite_residueField_adicCompletionIntegers NumberField.AdelicHaar.locallyCompactSpace_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_finiteAdeleRing NumberField.AdelicHaar.compactSpace_adicCompletionIntegers NumberField.AdelicHaar.t2Space_finiteAdeleRing NumberField.AdelicHaar.t2Space_matrix_adeleRing NumberField.AdelicHaar.t2Space_adeleRing NumberField.AdelicHaar.fact_isOpen_adicCompletionIntegers NumberField.AdelicHaar.t2Space_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_matrix_adeleRing NumberField.AdelicHaar.t2Space_infiniteAdeleRing NumberField.AdelicHaar.properSpace_adicCompletion M4aHerbrand.Bridge.instT2SpaceAdeleRing LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite"
p2m_attr_erase "instance" "Deep.NTSupply.instNormalRayClassSubgroup instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal AlgebraicClosure.Rat.isGalois groupCohomology.Kummer.instMulDistribMulActionRootsOfUnity groupCohomology.normal_comap_fixingSubgroup groupCohomology.finiteIndex_comap_fixingSubgroup Rep.relationCarrier.instAddCommGroup NumberField.LevelArith.instCommGroupUnitsModPow groupCohomology.instMulDistribMulActionGaloisSUnits"
p2m_attr_erase "simp" "M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk M4aHerbrand.IdeleGaloisDescent.classAct_mk M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq ExtCitation.LocalLevel.coe_smul_OO WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl NumberField.SUnits.val_zsmul NumberField.SUnits.val_add M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq"
p2m_attr_erase "simp" "FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq M4aHerbrand.Bridge.finiteConorm_apply SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul"
p2m_attr_erase "simp" "M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply"
p2m_attr_erase "simp" "RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq IsLocalRing.principalUnits_zero Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec groupCohomology.Kummer.coe_kummerCocycleRoots groupCohomology.Kummer.mem_powerSubgroup_iff groupCohomology.Kummer.val_smul_units groupCohomology.Kummer.kummerHom_apply groupCohomology.Kummer.coe_smul_rootsOfUnity groupCohomology.levelQuotientEquiv_mk groupCohomology.levelQuotientHom_mk"
p2m_attr_erase "simp" "Rep.toIntRepρ_apply_apply Rep.toIntRep_ρ Rep.toIntRepMap_hom_apply M4aHerbrand.AdeleBaseChange.classNorm_mk M4aHerbrand.AdeleBaseChange.coe_idelesMap_apply M4aHerbrand.AdeleBaseChange.classMap_mk M4aHerbrand.repHomResOfMulEquivariant_hom_apply M4aHerbrand.AdeleBaseChange.sClassNorm_mk M4aHerbrand.AdeleBaseChange.sClassMap_mk NumberField.SArchIdele.fibre_inl NumberField.SArchIdele.toSIdele_hom_apply_inr NumberField.SArchIdele.toSIdele_hom_apply_inl_inr NumberField.SArchIdele.toSIdele_hom_apply_inl_inl NumberField.SArchIdele.fibre_inr Representation.TateResCor.cosetDecomp_apply Rep.coe_tateHneg1Res_apply Representation.TateResCor.coe_tateHneg1Cores_apply Representation.TateResCor.tateH0Res_mk Rep.coe_tateHneg1Cores_apply Rep.tateH0Res_mk Representation.TateResCor.coe_cosetNormInvariants_apply Rep.tateH0Cores_mk Representation.TateResCor.coinvariantsCores_mk Representation.TateResCor.coinvariantsTransfer_mk Representation.TateResCor.tateH0Cores_mk Representation.TateResCor.coe_tateHneg1Res_apply Rep.coe_tateδneg2_apply Rep.splittingShortComplex_X₃ Rep.splittingShortComplex_X₁ Rep.splittingShortComplex_X₂ Rep.splittingShortComplex_f Rep.augShortComplex_f Rep.augShortComplex_X₃ Rep.cocycleTwist_single Rep.augShortComplex_X₂ Rep.splittingModuleι_hom_apply Rep.augShortComplex_X₁ Rep.splittingShortComplex_g Rep.augShortComplex_g Rep.splittingModuleπ_hom_apply"
p2m_attr_erase "simp" "Rep.coe_dimShiftDownObjMap_apply groupCohomology.continuousH2Inflation_H2π groupCohomology.levelInflate₂_apply groupCohomology.coe_levelInflateCocycles₂ groupCohomology.levelInflate₁_apply NumberField.LevelArith.coe_levelFieldEquiv NumberField.LevelArith.modP_apply_mk NumberField.LevelArith.coe_levelFieldEquiv_symm NumberField.LevelArith.torsionP_apply_coe NumberField.LevelArith.repTorsionPMap_hom_apply_coe NumberField.LevelArith.toZMod_apply NumberField.LevelArith.repModPMap_hom_mk groupCohomology.coe_continuousH1SrMap_apply groupCohomology.continuousH2SrMap_continuousH2Srπ groupCohomology.coe_levelCocyclesSr₂Map NumberField.LevelArith.smul_mk NumberField.LevelArith.selmerRepInt_ρ_apply NumberField.LevelArith.selmerRepField_ρ_apply NumberField.LevelArith.unitsModPowMap_mk groupCohomology.frobeniusOnCoinvariants_mk groupCohomology.evalAtGen_apply Rep.quotientRightTranslation_hom_single Rep.quotientRightTranslationTwist_hom_apply groupCohomology.coe_smul_galoisSUnits groupCohomology.galoisSUnitsToUnits_apply"

set_option autoImplicit false
p2m_open "CategoryTheory Module groupCohomology~inflation ExtCitation"

namespace DualAnnihilatorCount

universe u
variable {k : Type u} [Field k]

private noncomputable def pullAnn {V V' : Type u} [AddCommGroup V] [Module k V]
    [AddCommGroup V'] [Module k V'] (Φ : V ≃ₗ[k] Module.Dual k V')
    (U : Submodule k V') : Submodule k V :=
  U.dualAnnihilator.comap Φ.toLinearMap

private lemma mem_pullAnn_iff {V V' : Type u} [AddCommGroup V] [Module k V]
    [AddCommGroup V'] [Module k V'] (Φ : V ≃ₗ[k] Module.Dual k V')
    (U : Submodule k V') (v : V) :
    v ∈ pullAnn Φ U ↔ ∀ u ∈ U, Φ v u = 0 := by
  simp [pullAnn, Submodule.mem_comap, Submodule.mem_dualAnnihilator]

private lemma finrank_pullAnn {V V' : Type u} [AddCommGroup V] [Module k V]
    [AddCommGroup V'] [Module k V'] [FiniteDimensional k V']
    (Φ : V ≃ₗ[k] Module.Dual k V') (U : Submodule k V') :
    finrank k (pullAnn Φ U) + finrank k U = finrank k V' := by
  have h1 : finrank k (pullAnn Φ U) = finrank k U.dualAnnihilator := by
    rw [pullAnn, Submodule.comap_equiv_eq_map_symm]
    exact (Submodule.equivMapOfInjective _ Φ.symm.injective _).symm.finrank_eq
  rw [h1, add_comm]
  exact Subspace.finrank_add_finrank_dualAnnihilator_eq U

private theorem finrank_inf_add_finrank_pullAnn_sup {V V' : Type u} [AddCommGroup V] [Module k V]
    [AddCommGroup V'] [Module k V'] [FiniteDimensional k V']
    (Φ : V ≃ₗ[k] Module.Dual k V') (W' T' : Submodule k V') :
    finrank k (W' ⊓ T' : Submodule k V')
      + finrank k (pullAnn Φ W' ⊔ pullAnn Φ T' : Submodule k V)
      = finrank k V' := by
  have hsup : pullAnn Φ W' ⊔ pullAnn Φ T' = pullAnn Φ (W' ⊓ T') := by
    rw [pullAnn, pullAnn, pullAnn, Submodule.comap_equiv_eq_map_symm,
      Submodule.comap_equiv_eq_map_symm, Submodule.comap_equiv_eq_map_symm,
      ← Submodule.map_sup, ← Subspace.dualAnnihilator_inf_eq]
  rw [hsup, add_comm]
  exact finrank_pullAnn Φ (W' ⊓ T')

private noncomputable def dualPi {ι : Type u} [Fintype ι] [DecidableEq ι]
    (V : ι → Type u) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)] :
    Module.Dual k (∀ i, V i) ≃ₗ[k] ∀ i, Module.Dual k (V i) where
  toFun f i := f.comp (LinearMap.single k V i)
  map_add' f g := by ext i v; simp
  map_smul' c f := by ext i v; simp
  invFun g := ∑ i, (g i).comp (LinearMap.proj i)
  left_inv f := by
    ext v
    simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
      LinearMap.single_apply]
    rw [← map_sum, Finset.univ_sum_single]
  right_inv g := by
    ext i v
    simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
      LinearMap.single_apply]
    rw [Finset.sum_eq_single i]
    · rw [Pi.single_eq_same]
    · intro b _ hbi
      rw [Pi.single_eq_of_ne hbi, map_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h

@[scoped simp] private lemma dualPi_apply {ι : Type u} [Fintype ι] [DecidableEq ι]
    (V : ι → Type u) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
    (f : Module.Dual k (∀ i, V i)) (i : ι) (v : V i) :
    dualPi (k := k) V f i v = f (Pi.single i v) := by
  simp [dualPi]

end DualAnnihilatorCount
p2m_reactivate "P2MW.S_groupCohomology_greenbergWilesLeAdm_extArithLoc_of_isTheta1_eval_of_ne_two.DualAnnihilatorCount"

namespace GreenbergWilesLegs

universe u

private theorem exists_unit_smul_eq_of_bijective {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (f g : V →ₗ[K] K) (hf : Function.Bijective f) (hg : Function.Bijective g) :
    ∃ c : Kˣ, g = (c : K) • f := by
  obtain ⟨v, hv⟩ := hf.2 1
  have key : ∀ w : V, w = f w • v := fun w => hf.1 (by rw [map_smul, hv, smul_eq_mul, mul_one])
  have hgv : g v ≠ 0 := by
    intro h0
    have hv0 : v = 0 := hg.1 (by rw [h0, map_zero])
    rw [hv0, map_zero] at hv
    exact zero_ne_one hv
  refine ⟨Units.mk0 (g v) hgv, LinearMap.ext fun w => ?_⟩
  have hw := congrArg g (key w)
  rw [map_smul] at hw
  rw [hw, LinearMap.smul_apply, Units.val_mk0, smul_eq_mul, smul_eq_mul, mul_comm]

private theorem isTheta1_smul {k G : Type u} [CommRing k] [Group G]
    (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    {M D N : Rep.{u} k G} (φ : M →ₗ[k] D →ₗ[k] N) (inv : continuousH2 r N →ₗ[k] k)
    (θ : continuousH1 r M →ₗ[k] Module.Dual k (continuousH1 r D))
    (h : IsTheta1 r φ inv θ) (c : k) :
    IsTheta1 r φ (c • inv) (c • θ) := by
  intro f hf g hg e he
  rw [LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.smul_apply, h f hf g hg e he]

section Glue3

variable {k G : Type} [CommRing k] [Group G]

private theorem finiteDimensional_continuousH1_of_top {k G : Type} [Field k] [Group G]
    (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (M : Rep k G)
    (hFD : FiniteDimensional k
      (continuousH1 (r.comp (⊤ : Subgroup G).subtype) (Rep.res (⊤ : Subgroup G).subtype M))) :
    FiniteDimensional k (continuousH1 r M) := by
  haveI := hFD
  let f := (map (⊤ : Subgroup G).subtype (𝟙 (Rep.res (⊤ : Subgroup G).subtype M)) 1).hom
  let g : continuousH1 r M →ₗ[k]
      continuousH1 (r.comp (⊤ : Subgroup G).subtype) (Rep.res (⊤ : Subgroup G).subtype M) :=
    (f.comp (continuousH1 r M).subtype).codRestrict _
      (fun x => groupCohomology.map_apply_mem_continuousH1_comp r (⊤ : Subgroup G).subtype M x.1 x.2)
  refine FiniteDimensional.of_injective g ?_
  intro x y hxy
  apply Subtype.ext

  haveI : Subsingleton (G ⧸ (⊤ : Subgroup G)) := QuotientGroup.subsingleton_quotient_top
  haveI : Fintype (G ⧸ (⊤ : Subgroup G)) := Fintype.ofSubsingleton (1 : G ⧸ (⊤ : Subgroup G))
  have h1 : Fintype.card (G ⧸ (⊤ : Subgroup G)) = 1 :=
    Fintype.card_eq_one_iff.mpr ⟨1, fun b => Subsingleton.elim b 1⟩
  have hcard : ((Fintype.card (G ⧸ (⊤ : Subgroup G)) : k)) = 1 := by
    rw [h1, Nat.cast_one]
  have hinj := groupCohomology.injective_H1_restriction_of_isUnit_index
    (A := M) (S := (⊤ : Subgroup G)) (hcard ▸ isUnit_one)
  rw [groupCohomology.H1InfRes_g] at hinj
  exact hinj (congrArg Subtype.val hxy)

end Glue3
p2m_reactivate "P2MW.S_groupCohomology_greenbergWilesLeAdm_extArithLoc_of_isTheta1_eval_of_ne_two.DualAnnihilatorCount"

section Glue4

private theorem finrank_add_finrank_eq_of_range_eq_ker {K : Type*} [Field K] {V P D : Type*}
    [AddCommGroup V] [Module K V] [AddCommGroup P] [Module K P] [AddCommGroup D] [Module K D]
    [FiniteDimensional K V] [FiniteDimensional K P]
    (L : V →ₗ[K] P) (Θ : P →ₗ[K] D) (h : LinearMap.range L = LinearMap.ker Θ)
    (hΘ : Function.Surjective Θ) :
    finrank K V + finrank K D = finrank K (LinearMap.ker L) + finrank K P := by
  have e1 := LinearMap.finrank_range_add_finrank_ker L
  have e2 := LinearMap.finrank_range_add_finrank_ker Θ
  rw [h] at e1
  rw [LinearMap.range_eq_top.2 hΘ, finrank_top] at e2
  omega

end Glue4
p2m_reactivate "P2MW.S_groupCohomology_greenbergWilesLeAdm_extArithLoc_of_isTheta1_eval_of_ne_two.DualAnnihilatorCount"

section LocalData
variable {p : ℕ} (S : Finset Nat.Primes)
    (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))

private theorem hsm_loc (q : ↥S)
    (hsm : ∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s ∈ F.fixingSubgroup, M.ρ s m = m) :
    ∀ m : (Rep.res (extArithLoc S (Sum.inr q)) M),
      ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
        ∀ s, primeLocalToGlobal q.1 s ∈ F.fixingSubgroup →
          (Rep.res (extArithLoc S (Sum.inr q)) M).ρ s m = m := by
  intro m
  obtain ⟨F, hFD, hF⟩ := hsm m
  exact ⟨F, hFD, fun s hs => hF _ hs⟩

private theorem hadm₁_loc (q : ↥S) :
    ∀ x, x ∈ continuousH1 (extArithLoc S (Sum.inr q)) (Rep.res (extArithLoc S (Sum.inr q)) M) ↔
      ∃ c : cocycles₁ (Rep.res (extArithLoc S (Sum.inr q)) M),
        (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
          ∀ (g s : primeLocalGaloisGroup q.1),
            primeLocalToGlobal q.1 s ∈ F.fixingSubgroup → c.val (g * s) = c.val g)
        ∧ (H1π (Rep.res (extArithLoc S (Sum.inr q)) M)).hom c = x := by
  intro x
  exact mem_continuousH1_iff _ _ x

end LocalData
p2m_reactivate "P2MW.S_groupCohomology_greenbergWilesLeAdm_extArithLoc_of_isTheta1_eval_of_ne_two.DualAnnihilatorCount"

section MainInequality

variable
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    [FiniteDimensional (ZMod p) M]
    (hsm : ∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s ∈ F.fixingSubgroup, M.ρ s m = m)
    (hMur : ∀ q : Nat.Primes, q ∉ S → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
      A.LiesOverPrime (q : ℕ) → ∀ g ∈ A.inertiaSubgroupIn ℚ, M.ρ g = 1)
    (adm : Submodule (ZMod p) (H1 M))
    (hadm : ∀ x : H1 M, x ∈ adm ↔
      ∃ c : cocycles₁ M, IsLocallyConstant ⇑c ∧
        (∀ q : Nat.Primes, q ∉ S → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
          A.LiesOverPrime (q : ℕ) → ∃ m : M, ∀ g ∈ A.inertiaSubgroupIn ℚ, c g = M.ρ g m - m) ∧
        H1π M c = x)
    (adm' : Submodule (ZMod p) (H1 (M.dualTwist (cycloChar p))))
    (hadm' : ∀ x : H1 (M.dualTwist (cycloChar p)), x ∈ adm' ↔
      ∃ c : cocycles₁ (M.dualTwist (cycloChar p)), IsLocallyConstant ⇑c ∧
        (∀ q : Nat.Primes, q ∉ S → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
          A.LiesOverPrime (q : ℕ) → ∃ m : M.dualTwist (cycloChar p),
            ∀ g ∈ A.inertiaSubgroupIn ℚ, c g = (M.dualTwist (cycloChar p)).ρ g m - m) ∧
        H1π (M.dualTwist (cycloChar p)) c = x)
    (hinf : Subsingleton (H1 (Rep.res (extArithLoc S (Sum.inl ())) M)))
    (pairing : ∀ v : extArithIndex S,
      H1 (Rep.res (extArithLoc S v) M) →ₗ[ZMod p]
        H1 (Rep.res (extArithLoc S v) (M.dualTwist (cycloChar p))) →ₗ[ZMod p] ZMod p)
    (L : ∀ v, Submodule (ZMod p) (H1 (Rep.res (extArithLoc S v) M)))
    (hLcts : ∀ q : ↥S,
      L (Sum.inr q) ≤
        continuousH1 (extArithLoc S (Sum.inr q)) (Rep.res (extArithLoc S (Sum.inr q)) M))
    (inv : ∀ q : ↥S,
      continuousH2 (extArithLoc S (Sum.inr q))
          (ofChar (k := ZMod p) ((cycloChar p).comp (extArithLoc S (Sum.inr q)))) →ₗ[ZMod p]
        ZMod p)
    (hinv : ∀ q : ↥S, Function.Bijective (inv q))
    (θ : ∀ q : ↥S,
      continuousH1 (extArithLoc S (Sum.inr q)) (Rep.res (extArithLoc S (Sum.inr q)) M) →ₗ[ZMod p]
        Module.Dual (ZMod p)
          (continuousH1 (extArithLoc S (Sum.inr q))
            (Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p)))))
    (hθ : ∀ q : ↥S,
      IsTheta1 (extArithLoc S (Sum.inr q))
        (Module.Dual.eval (ZMod p) M :
          Rep.res (extArithLoc S (Sum.inr q)) M →ₗ[ZMod p]
            Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p)) →ₗ[ZMod p]
              ofChar (k := ZMod p) ((cycloChar p).comp (extArithLoc S (Sum.inr q))))
        (inv q) (θ q))
    (hbijθ : ∀ q : ↥S, Function.Bijective (θ q))
    (hagree : ∀ q : ↥S,
      ∀ (x : continuousH1 (extArithLoc S (Sum.inr q)) (Rep.res (extArithLoc S (Sum.inr q)) M))
        (y : continuousH1 (extArithLoc S (Sum.inr q))
              (Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p)))),
        pairing (Sum.inr q) (x : H1 _) (y : H1 _) = θ q x y)

include hpS hsm hMur in
private theorem arm_global_euler_char (hp2 : p ≠ 2) :
    finrank (ZMod p) M.ρ.invariants + finrank (ZMod p) (continuousH2S S M) + finrank (ZMod p) M
      = finrank (ZMod p) (continuousH1S S M)
        + finrank (ZMod p) (Rep.res (extArithLoc S (Sum.inl ())) M).ρ.invariants := by
  haveI : FiniteDimensional (ZMod p) (continuousH2S S M) :=
    TWNum.finiteDimensional_continuousH2S S hpS M hsm hMur
  exact groupCohomology.finrank_invariants_add_finrank_continuousH2S_add_finrank_eq_of_ne_two hp2 S hpS M hsm hMur

include hsm in
private theorem arm_fd_continuousH1_local (q : ↥S) :
    FiniteDimensional (ZMod p)
      (continuousH1 (extArithLoc S (Sum.inr q)) (Rep.res (extArithLoc S (Sum.inr q)) M)) := by

  have hT : ∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧
      F₀.fixingSubgroup.comap (primeLocalToGlobal q.1) ≤ (⊤ : Subgroup (primeLocalGaloisGroup q.1)) :=
    ⟨⊥, inferInstance, le_top⟩
  haveI : FiniteDimensional (ZMod p)
      (Rep.res (⊤ : Subgroup (primeLocalGaloisGroup q.1)).subtype
        (Rep.res (extArithLoc S (Sum.inr q)) M)) :=
    inferInstanceAs (FiniteDimensional (ZMod p) M)
  have hsmN : ∀ n : (Rep.res (⊤ : Subgroup (primeLocalGaloisGroup q.1)).subtype
        (Rep.res (extArithLoc S (Sum.inr q)) M)),
      ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
        ∀ s : (⊤ : Subgroup (primeLocalGaloisGroup q.1)),
          ((primeLocalToGlobal q.1).comp (⊤ : Subgroup _).subtype) s ∈ F.fixingSubgroup →
            (Rep.res (⊤ : Subgroup (primeLocalGaloisGroup q.1)).subtype
              (Rep.res (extArithLoc S (Sum.inr q)) M)).ρ s n = n := by
    intro n
    obtain ⟨F, hFD, hF⟩ := hsm n
    exact ⟨F, hFD, fun s hs => hF _ hs⟩
  have h9 := groupCohomology.finiteDimensional_continuousH1_of_isOpen_of_primeLocal (p := p) q.1 ⊤ hT
    (Rep.res (⊤ : Subgroup (primeLocalGaloisGroup q.1)).subtype (Rep.res (extArithLoc S (Sum.inr q)) M))
    hsmN
  exact finiteDimensional_continuousH1_of_top (primeLocalToGlobal q.1)
    (Rep.res (extArithLoc S (Sum.inr q)) M) h9

include hpS hsm in
private theorem arm_local_euler_char_at_p :
    finrank (ZMod p)
        (continuousH1 (extArithLoc S (Sum.inr ⟨pPrime p, hpS⟩))
          (Rep.res (extArithLoc S (Sum.inr ⟨pPrime p, hpS⟩)) M))
      = finrank (ZMod p) (Rep.res (extArithLoc S (Sum.inr ⟨pPrime p, hpS⟩)) M).ρ.invariants
        + finrank (ZMod p)
            ((Rep.res (extArithLoc S (Sum.inr ⟨pPrime p, hpS⟩)) M).dualTwist
              ((cycloChar p).comp (primeLocalToGlobal (pPrime p)))).ρ.invariants
        + finrank (ZMod p) (Rep.res (extArithLoc S (Sum.inr ⟨pPrime p, hpS⟩)) M) := by

  exact @groupCohomology.finrank_finiteQuotientH1_eq_invariants_add_dualTwist_add_finrank_of_primeLocal
    p _ (pPrime p) rfl (Rep.res (extArithLoc S (Sum.inr ⟨pPrime p, hpS⟩)) M)
    (inferInstanceAs (FiniteDimensional (ZMod p) M)) (hsm_loc S M ⟨pPrime p, hpS⟩ hsm)
    _ (arm_fd_continuousH1_local S M hsm ⟨pPrime p, hpS⟩) (hadm₁_loc S M ⟨pPrime p, hpS⟩)

include hsm in
private theorem arm_local_euler_char_ne_p (q : ↥S) (hne : ((q : Nat.Primes) : ℕ) ≠ p) :
    finrank (ZMod p)
        (continuousH1 (extArithLoc S (Sum.inr q)) (Rep.res (extArithLoc S (Sum.inr q)) M))
      = finrank (ZMod p) (Rep.res (extArithLoc S (Sum.inr q)) M).ρ.invariants
        + finrank (ZMod p)
            ((Rep.res (extArithLoc S (Sum.inr q)) M).dualTwist
              ((cycloChar p).comp (primeLocalToGlobal q.1))).ρ.invariants := by
  exact @groupCohomology.finrank_finiteQuotientH1_eq_invariants_add_dualTwist_of_primeLocal_ne
    p _ q.1 hne (Rep.res (extArithLoc S (Sum.inr q)) M)
    (inferInstanceAs (FiniteDimensional (ZMod p) M)) (hsm_loc S M q hsm)
    _ (arm_fd_continuousH1_local S M hsm q) (hadm₁_loc S M q)

omit [FiniteDimensional (ZMod p) M] in
include hinv hθ hbijθ in
private theorem arm_poitou_tate_h1 :
    ∃ (ζ : AlgebraicClosure ℚ) (_ : IsPrimitiveRoot ζ p)
      (c : ↥S → (ZMod p)ˣ),
      (∀ q : ↥S,
        haveI : Fact (((q : Nat.Primes) : ℕ)).Prime := ⟨(q : Nat.Primes).prop⟩
        IsTheta1 (extArithLoc S (Sum.inr q))
          (Module.Dual.eval (ZMod p) M :
            Rep.res (extArithLoc S (Sum.inr q)) M →ₗ[ZMod p]
              Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p)) →ₗ[ZMod p]
                ofChar (k := ZMod p) ((cycloChar p).comp (extArithLoc S (Sum.inr q))))
          (localInv p ζ (q : Nat.Primes)) ((c q : ZMod p) • θ q)) ∧
      (∀ q : ↥S, Function.Bijective ((c q : ZMod p) • θ q)) ∧
      (∀ (q : ↥S) x y, ((c q : ZMod p) • θ q) x y = 0 ↔ θ q x y = 0) := by
  haveI : NeZero ((p : ℕ) : ℚ) := ⟨Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) p
  have hc : ∀ q : ↥S, ∃ c : (ZMod p)ˣ,
      (haveI : Fact (((q : Nat.Primes) : ℕ)).Prime := ⟨(q : Nat.Primes).prop⟩
       localInv p ζ (q : Nat.Primes)) = (c : ZMod p) • inv q := by
    intro q
    haveI : Fact (((q : Nat.Primes) : ℕ)).Prime := ⟨(q : Nat.Primes).prop⟩
    exact exists_unit_smul_eq_of_bijective (inv q) (localInv p ζ (q : Nat.Primes)) (hinv q)
      (groupCohomology.isLocalInv_localInv_and_bijective p ζ hζ (q : Nat.Primes)).2
  choose c hc using hc
  refine ⟨ζ, hζ, c, fun q => ?_, fun q => ?_, fun q x y => ?_⟩
  · haveI : Fact (((q : Nat.Primes) : ℕ)).Prime := ⟨(q : Nat.Primes).prop⟩
    have h1 := isTheta1_smul (extArithLoc S (Sum.inr q)) _ (inv q) (θ q) (hθ q) (c q : ZMod p)
    rw [← hc q] at h1
    exact h1
  · have e : ((c q : ZMod p) • θ q)
        = (LinearEquiv.smulOfUnit (c q)).toLinearMap.comp (θ q) := by
      ext x y; rfl
    rw [e]
    exact (LinearEquiv.smulOfUnit (c q)).bijective.comp (hbijθ q)
  · rw [LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_zero]
    exact or_iff_right (c q).ne_zero

include hpS hsm hMur in
private theorem arm_sha1_dual_eq_sha2 (hp2 : p ≠ 2) :
    finrank (ZMod p) (sha₁ S (M.dualTwist (cycloChar p))) = finrank (ZMod p) (sha₂ S M) := by
  haveI : FiniteDimensional (ZMod p) (continuousH2S S M) :=
    TWNum.finiteDimensional_continuousH2S S hpS M hsm hMur
  exact groupCohomology.finrank_sha1_dualTwist_eq_finrank_sha2_of_ne_two hp2 S hpS M hsm hMur

omit [FiniteDimensional (ZMod p) M] in

private theorem isEquivariantBilinear_eval_res (q : ↥S) :
    Rep.IsEquivariantBilinear
      (Rep.res (extArithLoc S (Sum.inr q)) M)
      (Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p)))
      (ofChar (k := ZMod p) ((cycloChar p).comp (extArithLoc S (Sum.inr q))))
      (Module.Dual.eval (ZMod p) M :
        Rep.res (extArithLoc S (Sum.inr q)) M →ₗ[ZMod p]
          Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p)) →ₗ[ZMod p]
            ofChar (k := ZMod p) ((cycloChar p).comp (extArithLoc S (Sum.inr q)))) := by
  intro g m f
  change ((cycloChar p) (extArithLoc S (Sum.inr q) g) : ZMod p) •
      f (M.ρ (extArithLoc S (Sum.inr q) g)⁻¹ (M.ρ (extArithLoc S (Sum.inr q) g) m)) =
    ((cycloChar p) (extArithLoc S (Sum.inr q) g) : ZMod p) • f m
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

omit [FiniteDimensional (ZMod p) M] in
private theorem arm_exists_theta2 (ζ : AlgebraicClosure ℚ) :
    ∃ θ₂ : ∀ q : ↥S,
        continuousH2 (extArithLoc S (Sum.inr q)) (Rep.res (extArithLoc S (Sum.inr q)) M) →ₗ[ZMod p]
          Module.Dual (ZMod p) (Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p))).ρ.invariants,
      ∀ q : ↥S,
        haveI : Fact (((q : Nat.Primes) : ℕ)).Prime := ⟨(q : Nat.Primes).prop⟩
        IsTheta2 (extArithLoc S (Sum.inr q))
          (Module.Dual.eval (ZMod p) M :
            Rep.res (extArithLoc S (Sum.inr q)) M →ₗ[ZMod p]
              Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p)) →ₗ[ZMod p]
                ofChar (k := ZMod p) ((cycloChar p).comp (extArithLoc S (Sum.inr q))))
          (localInv p ζ (q : Nat.Primes)) (θ₂ q) := by
  have h : ∀ q : ↥S, ∃ θ₂ :
      continuousH2 (extArithLoc S (Sum.inr q)) (Rep.res (extArithLoc S (Sum.inr q)) M) →ₗ[ZMod p]
        Module.Dual (ZMod p) (Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p))).ρ.invariants,
      haveI : Fact (((q : Nat.Primes) : ℕ)).Prime := ⟨(q : Nat.Primes).prop⟩
      IsTheta2 (extArithLoc S (Sum.inr q))
        (Module.Dual.eval (ZMod p) M :
          Rep.res (extArithLoc S (Sum.inr q)) M →ₗ[ZMod p]
            Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p)) →ₗ[ZMod p]
              ofChar (k := ZMod p) ((cycloChar p).comp (extArithLoc S (Sum.inr q))))
        (localInv p ζ (q : Nat.Primes)) θ₂ := by
    intro q
    haveI : Fact (((q : Nat.Primes) : ℕ)).Prime := ⟨(q : Nat.Primes).prop⟩
    exact (groupCohomology.exists_theta0_and_theta2 (extArithLoc S (Sum.inr q)) _
      (isEquivariantBilinear_eval_res S M q) (localInv p ζ (q : Nat.Primes))).2
  choose θ₂ hθ₂ using h
  exact ⟨θ₂, hθ₂⟩

include hpS hsm hMur in
private theorem arm_h2_image_char (hp2 : p ≠ 2) (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p)
    (hinf2 : Subsingleton
      (continuousH2 (extArithLoc S (Sum.inl ())) (Rep.res (extArithLoc S (Sum.inl ())) M)))
    (θ₂ : ∀ q : ↥S,
      continuousH2 (extArithLoc S (Sum.inr q)) (Rep.res (extArithLoc S (Sum.inr q)) M) →ₗ[ZMod p]
        Module.Dual (ZMod p) (Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p))).ρ.invariants)
    (hθ₂ : ∀ q : ↥S,
      haveI : Fact (((q : Nat.Primes) : ℕ)).Prime := ⟨(q : Nat.Primes).prop⟩
      IsTheta2 (extArithLoc S (Sum.inr q))
        (Module.Dual.eval (ZMod p) M :
          Rep.res (extArithLoc S (Sum.inr q)) M →ₗ[ZMod p]
            Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p)) →ₗ[ZMod p]
              ofChar (k := ZMod p) ((cycloChar p).comp (extArithLoc S (Sum.inr q))))
        (localInv p ζ (q : Nat.Primes)) (θ₂ q)) :
    (∀ z : ∀ q : ↥S, continuousH2 (extArithLoc S (Sum.inr q)) (Rep.res (extArithLoc S (Sum.inr q)) M),
      (∃ x : continuousH2S S M, ∀ q : ↥S, locRes₂S S M (extArithLoc S (Sum.inr q)) x = z q) ↔
        ∀ d : (M.dualTwist (cycloChar p)).ρ.invariants,
          ∑ q : ↥S, θ₂ q (z q) ⟨(d : M.dualTwist (cycloChar p)), fun g => d.2 (extArithLoc S (Sum.inr q) g)⟩ = 0) ∧
    (∀ φ : Module.Dual (ZMod p) (M.dualTwist (cycloChar p)).ρ.invariants,
      ∃ z : ∀ q : ↥S, continuousH2 (extArithLoc S (Sum.inr q)) (Rep.res (extArithLoc S (Sum.inr q)) M),
        ∀ d : (M.dualTwist (cycloChar p)).ρ.invariants,
          ∑ q : ↥S, θ₂ q (z q) ⟨(d : M.dualTwist (cycloChar p)), fun g => d.2 (extArithLoc S (Sum.inr q) g)⟩ = φ d) :=
  groupCohomology.exists_continuousH2S_locRes_eq_iff_and_surjective_sum_theta2_of_ne_two
    hp2 S hpS M hsm hMur hinf2 ζ hζ θ₂ hθ₂

omit [FiniteDimensional (ZMod p) M] in

private theorem invariants_res_dualTwist_eq (q : ↥S) :
    ((Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p))).ρ.invariants :
        Submodule (ZMod p) (Module.Dual (ZMod p) M)) =
      ((Rep.res (extArithLoc S (Sum.inr q)) M).dualTwist
        ((cycloChar p).comp (primeLocalToGlobal q.1))).ρ.invariants := by
  ext f
  simp only [Representation.mem_invariants]
  refine forall_congr' fun g => ?_
  show ((cycloChar p (extArithLoc S (Sum.inr q) g) : ZMod p) •
          (f ∘ₗ M.ρ (extArithLoc S (Sum.inr q) g)⁻¹) = f) ↔
       (((cycloChar p).comp (primeLocalToGlobal q.1) g : ZMod p) •
          (f ∘ₗ M.ρ (extArithLoc S (Sum.inr q) g⁻¹)) = f)
  rw [show extArithLoc S (Sum.inr q) g⁻¹ = (extArithLoc S (Sum.inr q) g)⁻¹ from
    map_inv (extArithLoc S (Sum.inr q)) g]
  rfl

omit [FiniteDimensional (ZMod p) M] in

private theorem finrank_invariants_res_dualTwist_eq (q : ↥S) :
    finrank (ZMod p) (Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p))).ρ.invariants =
      finrank (ZMod p) ((Rep.res (extArithLoc S (Sum.inr q)) M).dualTwist
        ((cycloChar p).comp (primeLocalToGlobal q.1))).ρ.invariants :=
  congrArg (fun N : Submodule (ZMod p) (Module.Dual (ZMod p) M) => finrank (ZMod p) N)
    (invariants_res_dualTwist_eq S M q)

omit [FiniteDimensional (ZMod p) M] in

private noncomputable def resInv (q : ↥S) :
    (M.dualTwist (cycloChar p)).ρ.invariants →ₗ[ZMod p]
      (Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p))).ρ.invariants where
  toFun d := ⟨(d : M.dualTwist (cycloChar p)), fun g => d.2 (extArithLoc S (Sum.inr q) g)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

include hsm in

private theorem arm_th2dim_local (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p) (q : ↥S) :
    FiniteDimensional (ZMod p)
        (continuousH2 (extArithLoc S (Sum.inr q)) (Rep.res (extArithLoc S (Sum.inr q)) M)) ∧
      finrank (ZMod p)
          (continuousH2 (extArithLoc S (Sum.inr q)) (Rep.res (extArithLoc S (Sum.inr q)) M)) =
        finrank (ZMod p) ((Rep.res (extArithLoc S (Sum.inr q)) M).dualTwist
          ((cycloChar p).comp (primeLocalToGlobal q.1))).ρ.invariants := by
  haveI hq : Fact (((q : Nat.Primes) : ℕ)).Prime := ⟨(q : Nat.Primes).prop⟩

  let Mq : Rep (ZMod p) (primeLocalGaloisGroup q.1) := Rep.res (extArithLoc S (Sum.inr q)) M
  haveI hFDq : FiniteDimensional (ZMod p) Mq := ‹FiniteDimensional (ZMod p) M›
  let χq : primeLocalGaloisGroup q.1 →* (ZMod p)ˣ := (cycloChar p).comp (primeLocalToGlobal q.1)
  let φ : Mq →ₗ[ZMod p] Mq.dualTwist χq →ₗ[ZMod p] ofChar (k := ZMod p) χq :=
    (Module.Dual.eval (ZMod p) Mq : Mq →ₗ[ZMod p] Mq.dualTwist χq →ₗ[ZMod p] ofChar (k := ZMod p) χq)
  have hφ : Rep.IsEquivariantBilinear Mq (Mq.dualTwist χq) (ofChar (k := ZMod p) χq) φ :=
    Rep.isEquivariantBilinear_eval_dualTwist Mq χq
  have hsmq : ∀ m : Mq, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s, primeLocalToGlobal q.1 s ∈ F.fixingSubgroup → Mq.ρ s m = m :=
    hsm_loc S M q hsm

  obtain ⟨⟨θ₀, hθ₀⟩, ⟨θ₂, hθ₂⟩⟩ :=
    groupCohomology.exists_theta0_and_theta2 (primeLocalToGlobal q.1) φ hφ (localInv p ζ q.1)
  have hχ : ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s, primeLocalToGlobal q.1 s ∈ F.fixingSubgroup → χq s = 1 := by
    obtain ⟨F, hF, h⟩ := groupCohomology.exists_level_ofChar_cycloChar_comp (p := p)
      (primeLocalToGlobal q.1) (1 : ofChar (k := ZMod p) χq)
    refine ⟨F, hF, fun s hs => ?_⟩
    have h1 : ((χq s : (ZMod p)ˣ) : ZMod p) • (1 : ZMod p) = 1 := h s hs
    rw [smul_eq_mul, mul_one] at h1
    exact Units.val_eq_one.1 h1
  have hsmD := @Rep.dualTwist_smooth (ZMod p) (primeLocalGaloisGroup q.1) _ _
    (primeLocalToGlobal q.1) Mq hFDq χq hsmq hχ
  obtain ⟨θ₁, hθ₁⟩ :=
    groupCohomology.exists_theta1 (primeLocalToGlobal q.1) φ hφ hsmD (localInv p ζ q.1)

  have hbij := @groupCohomology.bijective_theta_dualTwist_of_primeLocal p _ q.1 Mq hFDq hsmq
    (localInv p ζ q.1) (groupCohomology.isLocalInv_localInv_and_bijective p ζ hζ q.1).2
    θ₀ hθ₀ θ₁ hθ₁ θ₂ hθ₂
  let e := LinearEquiv.ofBijective θ₂ hbij.2.2
  haveI : FiniteDimensional (ZMod p) (Mq.dualTwist χq) :=
    inferInstanceAs (FiniteDimensional (ZMod p) (Module.Dual (ZMod p) Mq))
  refine ⟨LinearEquiv.finiteDimensional e.symm, ?_⟩
  show finrank (ZMod p) (continuousH2 (primeLocalToGlobal q.1) Mq) =
    finrank (ZMod p) (Mq.dualTwist χq).ρ.invariants
  rw [e.finrank_eq, Subspace.dual_finrank_eq]

set_option maxHeartbeats 1600000 in
set_option maxSynthPendingDepth 3 in
include hpS hsm hMur hinf in

private theorem arm_th2dim (hp2 : p ≠ 2) (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p) :
    finrank (ZMod p) (continuousH2S S M) + finrank (ZMod p) (M.dualTwist (cycloChar p)).ρ.invariants =
      finrank (ZMod p) (sha₂ S M) +
        ∑ q : ↥S, finrank (ZMod p) ((Rep.res (extArithLoc S (Sum.inr q)) M).dualTwist
          ((cycloChar p).comp (primeLocalToGlobal q.1))).ρ.invariants := by
  classical
  haveI hFDH2S : FiniteDimensional (ZMod p) (continuousH2S S M) :=
    TWNum.finiteDimensional_continuousH2S S hpS M hsm hMur
  have hinf2 : Subsingleton
      (continuousH2 (extArithLoc S (Sum.inl ())) (Rep.res (extArithLoc S (Sum.inl ())) M)) :=
    TWNum.subsingleton_continuousH2_extArithLoc_inl S M hinf
  have h92 := arm_exists_theta2 S M ζ
  obtain ⟨θ₂, hθ₂⟩ := h92
  have hPT := groupCohomology.exists_continuousH2S_locRes_eq_iff_and_surjective_sum_theta2_of_ne_two
      hp2 S hpS M hsm hMur hinf2 ζ hζ θ₂ hθ₂
  obtain ⟨himg, hsurj⟩ := hPT
  have hloc := fun q : ↥S => arm_th2dim_local S M hsm ζ hζ q
  haveI : ∀ q : ↥S, FiniteDimensional (ZMod p)
      (continuousH2 (extArithLoc S (Sum.inr q)) (Rep.res (extArithLoc S (Sum.inr q)) M)) :=
    fun q => (hloc q).1
  haveI : FiniteDimensional (ZMod p) (M.dualTwist (cycloChar p)) :=
    inferInstanceAs (FiniteDimensional (ZMod p) (Module.Dual (ZMod p) M))

  let P := ∀ q : ↥S, continuousH2 (extArithLoc S (Sum.inr q)) (Rep.res (extArithLoc S (Sum.inr q)) M)
  let L : continuousH2S S M →ₗ[ZMod p] P :=
    LinearMap.pi fun q => locRes₂S S M (extArithLoc S (Sum.inr q))
  let Θ : P →ₗ[ZMod p] Module.Dual (ZMod p) (M.dualTwist (cycloChar p)).ρ.invariants :=
    ∑ q : ↥S, (resInv S M q).dualMap ∘ₗ θ₂ q ∘ₗ LinearMap.proj q
  have hΘ : ∀ (z : P) (d : (M.dualTwist (cycloChar p)).ρ.invariants),
      Θ z d = ∑ q : ↥S, θ₂ q (z q)
        ⟨(d : M.dualTwist (cycloChar p)), fun g => d.2 (extArithLoc S (Sum.inr q) g)⟩ := by
    intro z d
    simp only [Θ, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.dualMap_apply]
    rfl

  have hker : LinearMap.ker L = sha₂ S M := by
    ext x
    simp only [LinearMap.mem_ker, sha₂]
    constructor
    · intro h
      funext v
      rcases v with u | q
      · exact Subsingleton.elim _ _
      · exact congr_fun h q
    · intro h
      funext q
      exact congr_fun h (Sum.inr q)

  have hrange : LinearMap.range L = LinearMap.ker Θ := by
    ext z
    rw [LinearMap.mem_range, LinearMap.mem_ker]
    constructor
    · rintro ⟨x, rfl⟩
      apply LinearMap.ext
      intro d
      rw [hΘ, LinearMap.zero_apply]
      exact (himg (L x)).1 ⟨x, fun q => rfl⟩ d
    · intro hz
      have hz' : ∀ d : (M.dualTwist (cycloChar p)).ρ.invariants,
          ∑ q : ↥S, θ₂ q (z q)
            ⟨(d : M.dualTwist (cycloChar p)), fun g => d.2 (extArithLoc S (Sum.inr q) g)⟩ = 0 := by
        intro d
        rw [← hΘ, hz, LinearMap.zero_apply]
      obtain ⟨x, hx⟩ := (himg z).2 hz'
      exact ⟨x, funext hx⟩

  have hΘsurj : Function.Surjective Θ := by
    intro φ
    obtain ⟨z, hz⟩ := hsurj φ
    refine ⟨z, LinearMap.ext fun d => ?_⟩
    rw [hΘ]
    exact hz d

  have key : finrank (ZMod p) (continuousH2S S M) +
      finrank (ZMod p) (Module.Dual (ZMod p) (M.dualTwist (cycloChar p)).ρ.invariants) =
        finrank (ZMod p) (LinearMap.ker L) + finrank (ZMod p) P :=
    finrank_add_finrank_eq_of_range_eq_ker L Θ hrange hΘsurj
  rw [hker, Subspace.dual_finrank_eq] at key
  have eP : finrank (ZMod p) P =
      ∑ q : ↥S, finrank (ZMod p)
        (continuousH2 (extArithLoc S (Sum.inr q)) (Rep.res (extArithLoc S (Sum.inr q)) M)) :=
    Module.finrank_pi_fintype (ZMod p)
  have eS : ∑ q : ↥S, finrank (ZMod p)
        (continuousH2 (extArithLoc S (Sum.inr q)) (Rep.res (extArithLoc S (Sum.inr q)) M)) =
      ∑ q : ↥S, finrank (ZMod p) ((Rep.res (extArithLoc S (Sum.inr q)) M).dualTwist
        ((cycloChar p).comp (primeLocalToGlobal q.1))).ρ.invariants :=
    Finset.sum_congr rfl fun q _ => (hloc q).2
  rw [eP, eS] at key
  exact key

end MainInequality
p2m_reactivate "P2MW.S_groupCohomology_greenbergWilesLeAdm_extArithLoc_of_isTheta1_eval_of_ne_two.DualAnnihilatorCount"

end GreenbergWilesLegs
p2m_reactivate "P2MW.S_groupCohomology_greenbergWilesLeAdm_extArithLoc_of_isTheta1_eval_of_ne_two.DualAnnihilatorCount"

namespace DualTwistUnramified

private theorem cycloChar_eq_one_of_mem_inertiaSubgroupIn_of_ne
    {p : ℕ} [Fact p.Prime] (q : Nat.Primes) (hqp : (q : ℕ) ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime (q : ℕ))
    {g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hg : g ∈ A.inertiaSubgroupIn ℚ) :
    cycloChar p g = 1 := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

  have hqdvd : ¬ (q : ℕ) ∣ p :=
    fun hd => hqp ((Nat.prime_dvd_prime_iff_eq q.2 Fact.out).mp hd)

  have hfix : ∀ ζ : AlgebraicClosure ℚ, ζ ^ p = 1 → g ζ = ζ := fun ζ hζ =>
    ValuationSubring.apply_eq_self_of_pow_eq_one_of_mem_inertiaSubgroupIn q.2 A hA hg hqdvd hζ

  have hpgt : 1 < p := (Fact.out : p.Prime).one_lt
  have hc : ∀ t ∈ rootsOfUnity p (AlgebraicClosure ℚ),
      (g : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) t = t ^ (1 : ZMod p).val := by
    intro t ht
    rw [ZMod.val_one_eq_one_mod, Nat.one_mod_eq_one.mpr hpgt.ne', pow_one]
    have htp : (t : AlgebraicClosure ℚ) ^ p = 1 := (mem_rootsOfUnity' p t).mp ht
    exact_mod_cast hfix (↑t) htp
  have hunique := (modularCyclotomicCharacter.unique (L := AlgebraicClosure ℚ)
    (card_rootsOfUnity_eq_self p) (g : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) hc).symm

  exact Units.val_eq_one.mp hunique

private theorem arm_hMur'
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (hMur : ∀ q : Nat.Primes, q ∉ S → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
      A.LiesOverPrime (q : ℕ) → ∀ g ∈ A.inertiaSubgroupIn ℚ, M.ρ g = 1) :
    ∀ q : Nat.Primes, q ∉ S → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
      A.LiesOverPrime (q : ℕ) → ∀ g ∈ A.inertiaSubgroupIn ℚ,
        (M.dualTwist (cycloChar p)).ρ g = 1 := by
  intro q hqS A hA g hg
  have hqp : (q : ℕ) ≠ p := by
    intro h
    exact hqS ((Subtype.ext (h.trans (pPrime_coe p).symm) : q = pPrime p) ▸ hpS)
  have hχg : cycloChar p g = 1 :=
    cycloChar_eq_one_of_mem_inertiaSubgroupIn_of_ne q hqp A hA hg
  have hMρ : M.ρ g⁻¹ = 1 := hMur q hqS A hA g⁻¹ (Subgroup.inv_mem _ hg)
  refine LinearMap.ext fun f => ?_
  have happ := Rep.dualTwist_ρ_apply M (cycloChar p) g f
  rw [Module.End.one_eq_id, LinearMap.id_apply, happ, hχg, Units.val_one, one_smul, hMρ,
    Module.End.one_eq_id, LinearMap.comp_id]

end DualTwistUnramified
p2m_reactivate "P2MW.S_groupCohomology_greenbergWilesLeAdm_extArithLoc_of_isTheta1_eval_of_ne_two.DualAnnihilatorCount"

set_option maxHeartbeats 4000000 in
theorem solution
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    [FiniteDimensional (ZMod p) M]
    (hsm : ∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s ∈ F.fixingSubgroup, M.ρ s m = m)
    (hMur : ∀ q : Nat.Primes, q ∉ S → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
      A.LiesOverPrime (q : ℕ) → ∀ g ∈ A.inertiaSubgroupIn ℚ, M.ρ g = 1)
    (adm : Submodule (ZMod p) (H1 M))
    (hadm : ∀ x : H1 M, x ∈ adm ↔
      ∃ c : cocycles₁ M, IsLocallyConstant ⇑c ∧
        (∀ q : Nat.Primes, q ∉ S → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
          A.LiesOverPrime (q : ℕ) → ∃ m : M, ∀ g ∈ A.inertiaSubgroupIn ℚ, c g = M.ρ g m - m) ∧
        H1π M c = x)
    (adm' : Submodule (ZMod p) (H1 (M.dualTwist (cycloChar p))))
    (hadm' : ∀ x : H1 (M.dualTwist (cycloChar p)), x ∈ adm' ↔
      ∃ c : cocycles₁ (M.dualTwist (cycloChar p)), IsLocallyConstant ⇑c ∧
        (∀ q : Nat.Primes, q ∉ S → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
          A.LiesOverPrime (q : ℕ) → ∃ m : M.dualTwist (cycloChar p),
            ∀ g ∈ A.inertiaSubgroupIn ℚ, c g = (M.dualTwist (cycloChar p)).ρ g m - m) ∧
        H1π (M.dualTwist (cycloChar p)) c = x)
    (hinf : Subsingleton (H1 (Rep.res (extArithLoc S (Sum.inl ())) M)))
    (pairing : ∀ v : extArithIndex S,
      H1 (Rep.res (extArithLoc S v) M) →ₗ[ZMod p]
        H1 (Rep.res (extArithLoc S v) (M.dualTwist (cycloChar p))) →ₗ[ZMod p] ZMod p)
    (L : ∀ v, Submodule (ZMod p) (H1 (Rep.res (extArithLoc S v) M)))
    (hLcts : ∀ q : ↥S,
      L (Sum.inr q) ≤
        continuousH1 (extArithLoc S (Sum.inr q)) (Rep.res (extArithLoc S (Sum.inr q)) M))
    (inv : ∀ q : ↥S,
      continuousH2 (extArithLoc S (Sum.inr q))
          (ofChar (k := ZMod p) ((cycloChar p).comp (extArithLoc S (Sum.inr q)))) →ₗ[ZMod p]
        ZMod p)
    (hinv : ∀ q : ↥S, Function.Bijective (inv q))
    (θ : ∀ q : ↥S,
      continuousH1 (extArithLoc S (Sum.inr q)) (Rep.res (extArithLoc S (Sum.inr q)) M) →ₗ[ZMod p]
        Module.Dual (ZMod p)
          (continuousH1 (extArithLoc S (Sum.inr q))
            (Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p)))))
    (hθ : ∀ q : ↥S,
      IsTheta1 (extArithLoc S (Sum.inr q))
        (Module.Dual.eval (ZMod p) M :
          Rep.res (extArithLoc S (Sum.inr q)) M →ₗ[ZMod p]
            Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p)) →ₗ[ZMod p]
              ofChar (k := ZMod p) ((cycloChar p).comp (extArithLoc S (Sum.inr q))))
        (inv q) (θ q))
    (hbijθ : ∀ q : ↥S, Function.Bijective (θ q))
    (hagree : ∀ q : ↥S,
      ∀ (x : continuousH1 (extArithLoc S (Sum.inr q)) (Rep.res (extArithLoc S (Sum.inr q)) M))
        (y : continuousH1 (extArithLoc S (Sum.inr q))
              (Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p)))),
        pairing (Sum.inr q) (x : H1 _) (y : H1 _) = θ q x y) :
    greenbergWilesLeAdm (extArithLoc S) M (M.dualTwist (cycloChar p)) pairing L adm adm' := by
  classical

  have PH_hFDH2S : FiniteDimensional (ZMod p) (continuousH2S S M) :=
    TWNum.finiteDimensional_continuousH2S S hpS M hsm hMur
  have PH_hsm' : ∀ m : M.dualTwist (cycloChar p), ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ),
      FiniteDimensional ℚ F ∧ ∀ s ∈ F.fixingSubgroup, (M.dualTwist (cycloChar p)).ρ s m = m := by
    have hχ : ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
        ∀ s, (MonoidHom.id (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) s ∈ F.fixingSubgroup →
          cycloChar p s = 1 := by
      obtain ⟨F, hFD, hF⟩ := groupCohomology.exists_level_ofChar_cycloChar_comp
        (MonoidHom.id (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
        (1 : ofChar (k := ZMod p) ((cycloChar p).comp
          (MonoidHom.id (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))))
      refine ⟨F, hFD, fun s hs => ?_⟩
      have h1 := hF s hs
      have h2 : ((cycloChar p s : (ZMod p)ˣ) : ZMod p) * 1 = 1 := h1
      rw [mul_one] at h2
      exact Units.ext h2
    have hs' : ∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ),
        FiniteDimensional ℚ F ∧ ∀ s,
          (MonoidHom.id (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) s ∈ F.fixingSubgroup →
            M.ρ s m = m :=
      fun m => (hsm m).imp fun F h => ⟨h.1, fun s hs => h.2 s hs⟩
    exact Rep.dualTwist_smooth (MonoidHom.id _) M (cycloChar p) hs' hχ

  obtain ⟨ζ, hζ, c, hθc, hbijc, hzero⟩ := GreenbergWilesLegs.arm_poitou_tate_h1 S M inv hinv θ hθ hbijθ
  have PH_hMur' : ∀ q : Nat.Primes, q ∉ S → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
      A.LiesOverPrime (q : ℕ) → ∀ g ∈ A.inertiaSubgroupIn ℚ, (M.dualTwist (cycloChar p)).ρ g = 1 :=
    DualTwistUnramified.arm_hMur' S hpS M hMur
  haveI PH_hinf' : Subsingleton (H1 (Rep.res (extArithLoc S (Sum.inl ()))
      (M.dualTwist (cycloChar p)))) :=
    TWNum.subsingleton_H1_extArithLoc_inl_dualTwist S M (cycloChar p) hinf
  have ARM_th2dim : finrank (ZMod p) (continuousH2S S M)
        + finrank (ZMod p) (M.dualTwist (cycloChar p)).ρ.invariants
      = finrank (ZMod p) (sha₂ S M)
        + (∑ q : ↥S, finrank (ZMod p) ((Rep.res (extArithLoc S (Sum.inr q)) M).dualTwist
            ((cycloChar p).comp (primeLocalToGlobal q.1))).ρ.invariants) :=
    GreenbergWilesLegs.arm_th2dim S hpS M hsm hMur hinf hp2 ζ hζ

  have hadm_eq : adm = continuousH1S S M :=
    groupCohomology.eq_continuousH1S_of_forall_mem_iff S M hMur adm hadm
  have hadm'_eq : adm' = continuousH1S S (M.dualTwist (cycloChar p)) :=
    groupCohomology.eq_continuousH1S_of_forall_mem_iff S (M.dualTwist (cycloChar p))
      PH_hMur' adm' hadm'

  haveI hFD1 : FiniteDimensional (ZMod p) (continuousH1S S M) :=
    groupCohomology.finiteDimensional_continuousH1S S M hsm
  haveI hFDM' : FiniteDimensional (ZMod p) (M.dualTwist (cycloChar p)) :=
    Subspace.instModuleDualFiniteDimensional.{0}
  haveI hFD1' : FiniteDimensional (ZMod p) (continuousH1S S (M.dualTwist (cycloChar p))) :=
    groupCohomology.finiteDimensional_continuousH1S S (M.dualTwist (cycloChar p)) PH_hsm'
  haveI : FiniteDimensional (ZMod p) adm := hadm_eq ▸ hFD1
  haveI : FiniteDimensional (ZMod p) adm' := hadm'_eq ▸ hFD1'

  have hmem_loc : ∀ (x : H1 M), x ∈ adm → ∀ q : ↥S,
      (locRes (extArithLoc S) M (Sum.inr q)).hom x ∈
        continuousH1 (extArithLoc S (Sum.inr q)) (Rep.res (extArithLoc S (Sum.inr q)) M) := by
    intro x hx q
    exact groupCohomology.locRes_extArithLoc_apply_mem_continuousH1 S M x
      (groupCohomology.continuousH1S_le_continuousH1 S M (hadm_eq ▸ hx)) (Sum.inr q)
  have hmem_loc' : ∀ (y : H1 (M.dualTwist (cycloChar p))), y ∈ adm' → ∀ q : ↥S,
      (locRes (extArithLoc S) (M.dualTwist (cycloChar p)) (Sum.inr q)).hom y ∈
        continuousH1 (extArithLoc S (Sum.inr q))
          (Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p))) := by
    intro y hy q
    exact groupCohomology.locRes_extArithLoc_apply_mem_continuousH1 S (M.dualTwist (cycloChar p)) y
      (groupCohomology.continuousH1S_le_continuousH1 S (M.dualTwist (cycloChar p))
        (hadm'_eq ▸ hy)) (Sum.inr q)
  let φ : adm →ₗ[ZMod p] ∀ q : ↥S,
      continuousH1 (extArithLoc S (Sum.inr q)) (Rep.res (extArithLoc S (Sum.inr q)) M) :=
    LinearMap.pi fun q => LinearMap.codRestrict _
      (((locRes (extArithLoc S) M (Sum.inr q)).hom).comp adm.subtype)
      (fun x => hmem_loc x.1 x.2 q)
  let φ' : adm' →ₗ[ZMod p] ∀ q : ↥S,
      continuousH1 (extArithLoc S (Sum.inr q))
        (Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p))) :=
    LinearMap.pi fun q => LinearMap.codRestrict _
      (((locRes (extArithLoc S) (M.dualTwist (cycloChar p)) (Sum.inr q)).hom).comp adm'.subtype)
      (fun y => hmem_loc' y.1 y.2 q)

  let Φ : (∀ q : ↥S, continuousH1 (extArithLoc S (Sum.inr q))
        (Rep.res (extArithLoc S (Sum.inr q)) M)) ≃ₗ[ZMod p]
      Module.Dual (ZMod p) (∀ q : ↥S, continuousH1 (extArithLoc S (Sum.inr q))
        (Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p)))) :=
    (LinearEquiv.piCongrRight fun q => LinearEquiv.ofBijective ((c q : ZMod p) • θ q) (hbijc q)).trans
      (DualAnnihilatorCount.dualPi _).symm
  have hΦ_apply : ∀ z w, Φ z w = ∑ q : ↥S, ((c q : ZMod p) • θ q) (z q) (w q) := by
    intro z w
    show (∑ q : ↥S, (((c q : ZMod p) • θ q) (z q)).comp (LinearMap.proj q)) w = _
    rw [LinearMap.sum_apply]
    rfl

  have hE3 : LinearMap.range φ = DualAnnihilatorCount.pullAnn Φ (LinearMap.range φ') := by
    ext z
    rw [DualAnnihilatorCount.mem_pullAnn_iff]
    constructor
    · rintro ⟨x, rfl⟩ w ⟨y, rfl⟩
      have h5 := (groupCohomology.exists_mem_continuousH1S_locRes_eq_iff_forall_sum_theta_eq_zero_of_ne_two
        hp2 S hpS M hsm hMur hinf ζ hζ (fun q => ((c q : ZMod p) • θ q)) hθc (fun q => φ x q)).mp
        ⟨x.1, hadm_eq ▸ x.2, fun q => rfl⟩
      rw [hΦ_apply]
      exact h5 y.1 (hadm'_eq ▸ y.2) (fun q => φ' y q) (fun q => rfl)
    · intro hz
      have h5 := (groupCohomology.exists_mem_continuousH1S_locRes_eq_iff_forall_sum_theta_eq_zero_of_ne_two
        hp2 S hpS M hsm hMur hinf ζ hζ (fun q => ((c q : ZMod p) • θ q)) hθc (fun q => z q)).mpr
      obtain ⟨x, hxS, hxloc⟩ := h5 (by
        intro y hy w hw
        have := hz (φ' ⟨y, hadm'_eq.symm ▸ hy⟩) ⟨⟨y, hadm'_eq.symm ▸ hy⟩, rfl⟩
        rw [hΦ_apply] at this
        have hwc : w = fun q => φ' ⟨y, hadm'_eq.symm ▸ hy⟩ q := by
          funext q
          exact Subtype.ext (hw q)
        rw [hwc]
        exact this)
      refine ⟨⟨x, hadm_eq.symm ▸ hxS⟩, ?_⟩
      funext q
      exact Subtype.ext (hxloc q)

  let θe : ∀ q : ↥S, (continuousH1 (extArithLoc S (Sum.inr q))
        (Rep.res (extArithLoc S (Sum.inr q)) M)) ≃ₗ[ZMod p]
      Module.Dual (ZMod p) (continuousH1 (extArithLoc S (Sum.inr q))
        (Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p)))) :=
    fun q => LinearEquiv.ofBijective ((c q : ZMod p) • θ q) (hbijc q)

  have hpullPi : ∀ (U : ∀ q : ↥S, Submodule (ZMod p) (continuousH1 (extArithLoc S (Sum.inr q))
        (Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p))))),
      DualAnnihilatorCount.pullAnn Φ (Submodule.pi Set.univ U)
        = Submodule.pi Set.univ (fun q => DualAnnihilatorCount.pullAnn (θe q) (U q)) := by
    intro U
    ext z
    rw [DualAnnihilatorCount.mem_pullAnn_iff, Submodule.mem_pi]
    constructor
    · intro hz q _
      rw [DualAnnihilatorCount.mem_pullAnn_iff]
      intro u hu
      have hone := hz (Pi.single q u) (by
        rw [Submodule.mem_pi]
        intro i _
        by_cases hiq : i = q
        · subst hiq; rw [Pi.single_eq_same]; exact hu
        · rw [Pi.single_eq_of_ne hiq]; exact (U i).zero_mem)
      rw [hΦ_apply, Finset.sum_eq_single q] at hone
      · rwa [Pi.single_eq_same] at hone
      · intro b _ hbq; rw [Pi.single_eq_of_ne hbq, map_zero]
      · intro h; exact absurd (Finset.mem_univ q) h
    · intro hz w hw
      rw [hΦ_apply]
      refine Finset.sum_eq_zero fun q _ => ?_
      have := hz q (Set.mem_univ q)
      rw [DualAnnihilatorCount.mem_pullAnn_iff] at this
      exact this (w q) (Submodule.mem_pi.mp hw q (Set.mem_univ q))

  have hLc_mem : ∀ q : ↥S, ∀ (l : continuousH1 (extArithLoc S (Sum.inr q))
      (Rep.res (extArithLoc S (Sum.inr q)) M)),
      l ∈ (L (Sum.inr q)).comap (continuousH1 (extArithLoc S (Sum.inr q))
        (Rep.res (extArithLoc S (Sum.inr q)) M)).subtype ↔ (l : H1 _) ∈ L (Sum.inr q) :=
    fun q l => Iff.rfl
  have hE5q : ∀ q : ↥S,
      (L (Sum.inr q)).comap (continuousH1 (extArithLoc S (Sum.inr q))
          (Rep.res (extArithLoc S (Sum.inr q)) M)).subtype
        = DualAnnihilatorCount.pullAnn (θe q)
            ((dualConditions (extArithLoc S) M (M.dualTwist (cycloChar p))
              pairing L (Sum.inr q)).comap
                (continuousH1 (extArithLoc S (Sum.inr q))
                  (Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p)))).subtype) := by
    intro q

    let flipE : (continuousH1 (extArithLoc S (Sum.inr q))
          (Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p)))) ≃ₗ[ZMod p]
        Module.Dual (ZMod p) (continuousH1 (extArithLoc S (Sum.inr q))
          (Rep.res (extArithLoc S (Sum.inr q)) M)) :=
      haveI := GreenbergWilesLegs.arm_fd_continuousH1_local S (M.dualTwist (cycloChar p)) PH_hsm' q
      (Module.evalEquiv (ZMod p) _).trans (θe q).dualMap
    have hflip_apply : ∀ w v, flipE w v = ((c q : ZMod p) • θ q) v w := fun w v => rfl

    have hdc : (dualConditions (extArithLoc S) M (M.dualTwist (cycloChar p))
          pairing L (Sum.inr q)).comap
            (continuousH1 (extArithLoc S (Sum.inr q))
              (Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p)))).subtype
        = DualAnnihilatorCount.pullAnn flipE ((L (Sum.inr q)).comap
            (continuousH1 (extArithLoc S (Sum.inr q))
              (Rep.res (extArithLoc S (Sum.inr q)) M)).subtype) := by
      ext w
      rw [DualAnnihilatorCount.mem_pullAnn_iff]
      constructor
      · intro hw l hl
        have hw2 : (w : H1 _) ∈ orthogonal (pairing (Sum.inr q)) (L (Sum.inr q)) := hw
        have hv := (mem_orthogonal_iff (pairing (Sum.inr q)) (L (Sum.inr q)) (w : H1 _)).mp hw2
          (l : H1 _) hl
        rw [hagree q l w] at hv
        rw [hflip_apply]
        exact (hzero q l w).mpr hv
      · intro hw
        show (w : H1 _) ∈ orthogonal (pairing (Sum.inr q)) (L (Sum.inr q))
        rw [mem_orthogonal_iff]
        intro x hx
        have hv := hw ⟨x, hLcts q hx⟩ hx
        rw [hflip_apply] at hv
        rw [hagree q ⟨x, hLcts q hx⟩ w]
        exact (hzero q ⟨x, hLcts q hx⟩ w).mp hv
    rw [hdc]

    haveI := GreenbergWilesLegs.arm_fd_continuousH1_local S M hsm q
    haveI := GreenbergWilesLegs.arm_fd_continuousH1_local S (M.dualTwist (cycloChar p)) PH_hsm' q
    have hle : (L (Sum.inr q)).comap (continuousH1 (extArithLoc S (Sum.inr q))
          (Rep.res (extArithLoc S (Sum.inr q)) M)).subtype
        ≤ DualAnnihilatorCount.pullAnn (θe q) (DualAnnihilatorCount.pullAnn flipE
            ((L (Sum.inr q)).comap (continuousH1 (extArithLoc S (Sum.inr q))
              (Rep.res (extArithLoc S (Sum.inr q)) M)).subtype)) := by
      intro l hl
      rw [DualAnnihilatorCount.mem_pullAnn_iff]
      intro w hw
      rw [DualAnnihilatorCount.mem_pullAnn_iff] at hw
      have := hw l hl
      rw [hflip_apply] at this
      exact this
    have hdim : finrank (ZMod p) (DualAnnihilatorCount.pullAnn (θe q) (DualAnnihilatorCount.pullAnn flipE
          ((L (Sum.inr q)).comap (continuousH1 (extArithLoc S (Sum.inr q))
            (Rep.res (extArithLoc S (Sum.inr q)) M)).subtype)))
        ≤ finrank (ZMod p) ((L (Sum.inr q)).comap (continuousH1 (extArithLoc S (Sum.inr q))
            (Rep.res (extArithLoc S (Sum.inr q)) M)).subtype) := by
      have h1 := DualAnnihilatorCount.finrank_pullAnn (θe q) (DualAnnihilatorCount.pullAnn flipE
        ((L (Sum.inr q)).comap (continuousH1 (extArithLoc S (Sum.inr q))
          (Rep.res (extArithLoc S (Sum.inr q)) M)).subtype))
      have h2 := DualAnnihilatorCount.finrank_pullAnn flipE
        ((L (Sum.inr q)).comap (continuousH1 (extArithLoc S (Sum.inr q))
          (Rep.res (extArithLoc S (Sum.inr q)) M)).subtype)
      have h3 : finrank (ZMod p) (continuousH1 (extArithLoc S (Sum.inr q))
            (Rep.res (extArithLoc S (Sum.inr q)) M))
          = finrank (ZMod p) (Module.Dual (ZMod p) (continuousH1 (extArithLoc S (Sum.inr q))
              (Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p))))) :=
        LinearEquiv.finrank_eq (θe q)
      have h4 : finrank (ZMod p) (Module.Dual (ZMod p) (continuousH1 (extArithLoc S (Sum.inr q))
            (Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p)))))
          = finrank (ZMod p) (continuousH1 (extArithLoc S (Sum.inr q))
              (Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p)))) :=
        Subspace.dual_finrank_eq
      omega
    exact Submodule.eq_of_le_of_finrank_le hle hdim

  have hE5 : Submodule.pi Set.univ (fun q : ↥S => (L (Sum.inr q)).comap
        (continuousH1 (extArithLoc S (Sum.inr q))
          (Rep.res (extArithLoc S (Sum.inr q)) M)).subtype)
      = DualAnnihilatorCount.pullAnn Φ (Submodule.pi Set.univ
          (fun q : ↥S => (dualConditions (extArithLoc S) M (M.dualTwist (cycloChar p))
            pairing L (Sum.inr q)).comap
              (continuousH1 (extArithLoc S (Sum.inr q))
                (Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p)))).subtype)) := by
    rw [hpullPi]
    exact congrArg (Submodule.pi Set.univ) (funext hE5q)

  have hbridgeA : Submodule.comap adm.subtype (selmerAdm (extArithLoc S) M L adm)
      = (Submodule.pi Set.univ (fun q : ↥S => (L (Sum.inr q)).comap
          (continuousH1 (extArithLoc S (Sum.inr q))
            (Rep.res (extArithLoc S (Sum.inr q)) M)).subtype)).comap φ := by
    ext x
    simp only [Submodule.mem_comap, mem_selmerAdm_iff, Submodule.mem_pi, Set.mem_univ,
      forall_true_left]
    constructor
    · rintro ⟨hv, _⟩ q
      exact hv (Sum.inr q)
    · intro hq
      refine ⟨fun v => ?_, x.2⟩
      rcases v with u | q
      · have h0 : (locRes (extArithLoc S) M (Sum.inl u)).hom (adm.subtype x) = 0 :=
          Subsingleton.elim _ _
        rw [show (Sum.inl u : extArithIndex S) = Sum.inl () from rfl] at h0 ⊢
        rw [h0]
        exact (L (Sum.inl ())).zero_mem
      · exact hq q
  have hSelA : finrank (ZMod p) (selmerAdm (extArithLoc S) M L adm)
      = finrank (ZMod p) ((Submodule.pi Set.univ (fun q : ↥S => (L (Sum.inr q)).comap
          (continuousH1 (extArithLoc S (Sum.inr q))
            (Rep.res (extArithLoc S (Sum.inr q)) M)).subtype)).comap φ) :=
    ((LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe
      (inf_le_right : selmerAdm (extArithLoc S) M L adm ≤ adm))).symm).trans
      (congrArg (fun N : Submodule (ZMod p) adm => finrank (ZMod p) N) hbridgeA)
  have hbridgeA' : Submodule.comap adm'.subtype (selmerAdm (extArithLoc S)
        (M.dualTwist (cycloChar p))
        (dualConditions (extArithLoc S) M (M.dualTwist (cycloChar p)) pairing L) adm')
      = (Submodule.pi Set.univ
          (fun q : ↥S => (dualConditions (extArithLoc S) M (M.dualTwist (cycloChar p))
            pairing L (Sum.inr q)).comap
              (continuousH1 (extArithLoc S (Sum.inr q))
                (Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p)))).subtype)).comap φ' := by
    ext y
    simp only [Submodule.mem_comap, mem_selmerAdm_iff, Submodule.mem_pi, Set.mem_univ,
      forall_true_left]
    constructor
    · rintro ⟨hv, _⟩ q
      exact hv (Sum.inr q)
    · intro hq
      refine ⟨fun v => ?_, y.2⟩
      rcases v with u | q
      · have h0 : (locRes (extArithLoc S) (M.dualTwist (cycloChar p)) (Sum.inl u)).hom
            (adm'.subtype y) = 0 := Subsingleton.elim _ _
        rw [show (Sum.inl u : extArithIndex S) = Sum.inl () from rfl] at h0 ⊢
        rw [h0]
        exact (dualConditions (extArithLoc S) M (M.dualTwist (cycloChar p)) pairing L
          (Sum.inl ())).zero_mem
      · exact hq q
  have hSelA' : finrank (ZMod p) (selmerAdm (extArithLoc S) (M.dualTwist (cycloChar p))
        (dualConditions (extArithLoc S) M (M.dualTwist (cycloChar p)) pairing L) adm')
      = finrank (ZMod p) ((Submodule.pi Set.univ
          (fun q : ↥S => (dualConditions (extArithLoc S) M (M.dualTwist (cycloChar p))
            pairing L (Sum.inr q)).comap
              (continuousH1 (extArithLoc S (Sum.inr q))
                (Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p)))).subtype)).comap φ') :=
    ((LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe
      (inf_le_right : selmerAdm (extArithLoc S) (M.dualTwist (cycloChar p))
        (dualConditions (extArithLoc S) M (M.dualTwist (cycloChar p)) pairing L) adm' ≤ adm'))).symm).trans
      (congrArg (fun N : Submodule (ZMod p) adm' => finrank (ZMod p) N) hbridgeA')

  haveI := PH_hFDH2S
  haveI : ∀ q : ↥S, FiniteDimensional (ZMod p) (continuousH1 (extArithLoc S (Sum.inr q))
      (Rep.res (extArithLoc S (Sum.inr q)) M)) := fun q => GreenbergWilesLegs.arm_fd_continuousH1_local S M hsm q
  haveI : ∀ q : ↥S, FiniteDimensional (ZMod p) (continuousH1 (extArithLoc S (Sum.inr q))
      (Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p)))) :=
    fun q => GreenbergWilesLegs.arm_fd_continuousH1_local S (M.dualTwist (cycloChar p)) PH_hsm' q
  have eA := Submodule.finrank_comap_eq_finrank_ker_add_finrank_range_inf φ (Submodule.pi Set.univ
    (fun q : ↥S => (L (Sum.inr q)).comap (continuousH1 (extArithLoc S (Sum.inr q))
      (Rep.res (extArithLoc S (Sum.inr q)) M)).subtype))
  have eA' := Submodule.finrank_comap_eq_finrank_ker_add_finrank_range_inf φ' (Submodule.pi Set.univ
    (fun q : ↥S => (dualConditions (extArithLoc S) M (M.dualTwist (cycloChar p))
      pairing L (Sum.inr q)).comap
        (continuousH1 (extArithLoc S (Sum.inr q))
          (Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p)))).subtype))
  have e2 := LinearMap.finrank_range_add_finrank_ker φ
  have e2' := LinearMap.finrank_range_add_finrank_ker φ'
  have e4 := DualAnnihilatorCount.finrank_inf_add_finrank_pullAnn_sup Φ
    (LinearMap.range φ')
    (Submodule.pi Set.univ (fun q : ↥S => (dualConditions (extArithLoc S) M
      (M.dualTwist (cycloChar p)) pairing L (Sum.inr q)).comap
        (continuousH1 (extArithLoc S (Sum.inr q))
          (Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p)))).subtype))
  rw [← hE3, ← hE5] at e4
  have e5 := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range φ)
    (Submodule.pi Set.univ (fun q : ↥S => (L (Sum.inr q)).comap
      (continuousH1 (extArithLoc S (Sum.inr q))
        (Rep.res (extArithLoc S (Sum.inr q)) M)).subtype))
  have e6 : finrank (ZMod p) (Submodule.pi Set.univ (fun q : ↥S => (L (Sum.inr q)).comap
        (continuousH1 (extArithLoc S (Sum.inr q))
          (Rep.res (extArithLoc S (Sum.inr q)) M)).subtype))
      = ∑ q : ↥S, finrank (ZMod p) (L (Sum.inr q)) := by
    rw [Submodule.finrank_pi_univ_eq_sum]
    exact Finset.sum_congr rfl fun q _ =>
      LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe (hLcts q))
  have e7 : finrank (ZMod p) (∀ q : ↥S, continuousH1 (extArithLoc S (Sum.inr q))
        (Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p))))
      = ∑ q : ↥S, finrank (ZMod p) (continuousH1 (extArithLoc S (Sum.inr q))
          (Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p)))) :=
    Module.finrank_pi_fintype _
  have e8 : ∀ q : ↥S, finrank (ZMod p) (continuousH1 (extArithLoc S (Sum.inr q))
        (Rep.res (extArithLoc S (Sum.inr q)) M))
      = finrank (ZMod p) (continuousH1 (extArithLoc S (Sum.inr q))
          (Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p)))) :=
    fun q => (LinearEquiv.finrank_eq (θe q)).trans Subspace.dual_finrank_eq

  have hbridge9 : Submodule.comap adm'.subtype (sha₁ S (M.dualTwist (cycloChar p)))
      = LinearMap.ker φ' := by
    ext y
    simp only [Submodule.mem_comap, LinearMap.mem_ker, sha₁, Submodule.mem_inf]
    constructor
    · rintro ⟨_, hk⟩
      funext q
      exact Subtype.ext (congrFun hk (Sum.inr q))
    · intro h0
      refine ⟨hadm'_eq ▸ y.2, ?_⟩
      funext v
      rcases v with u | q
      · rw [show (Sum.inl u : extArithIndex S) = Sum.inl () from rfl]
        exact Subsingleton.elim _ _
      · have := congrArg Subtype.val (congrFun h0 q)
        first | simpa using this | (have h_1 := this; simp at h_1; exact h_1) | (have h_1 := this; simp at h_1 ⊢; exact h_1) | exact (this)
  have e9 : finrank (ZMod p) (LinearMap.ker φ')
      = finrank (ZMod p) (sha₁ S (M.dualTwist (cycloChar p))) := by
    rw [← hbridge9]
    exact (LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe
      (show sha₁ S (M.dualTwist (cycloChar p)) ≤ adm' from hadm'_eq ▸ inf_le_left)))
  have e10 : finrank (ZMod p) (sha₁ S (M.dualTwist (cycloChar p)))
      = finrank (ZMod p) (sha₂ S M) :=
    groupCohomology.finrank_sha1_dualTwist_eq_finrank_sha2_of_ne_two hp2 S hpS M hsm hMur
  have e11 := groupCohomology.finrank_invariants_add_finrank_continuousH2S_add_finrank_eq_of_ne_two
    hp2 S hpS M hsm hMur
  have e12 : finrank (ZMod p) adm = finrank (ZMod p) (continuousH1S S M) := by rw [hadm_eq]

  have esplit1 : (∑ v, finrank (ZMod p) (Rep.res (extArithLoc S v) M).ρ.invariants)
      = finrank (ZMod p) (Rep.res (extArithLoc S (Sum.inl ())) M).ρ.invariants
        + ∑ q : ↥S, finrank (ZMod p) (Rep.res (extArithLoc S (Sum.inr q)) M).ρ.invariants := by
    rw [show (∑ v, finrank (ZMod p) (Rep.res (extArithLoc S v) M).ρ.invariants)
        = ∑ v : Unit ⊕ ↥S, finrank (ZMod p) (Rep.res (extArithLoc S v) M).ρ.invariants from rfl,
      Fintype.sum_sum_type]
    congr 1
  have esplit2 : (∑ v, finrank (ZMod p) (L v))
      = finrank (ZMod p) (L (Sum.inl ())) + ∑ q : ↥S, finrank (ZMod p) (L (Sum.inr q)) := by
    rw [show (∑ v, finrank (ZMod p) (L v))
        = ∑ v : Unit ⊕ ↥S, finrank (ZMod p) (L v) from rfl,
      Fintype.sum_sum_type]
    congr 1
  have harchL : finrank (ZMod p) (L (Sum.inl ())) = 0 :=
    finrank_zero_of_subsingleton

  rw [greenbergWilesLeAdm, hSelA, hSelA', esplit1, esplit2, harchL]
  have hEP : ∀ q : ↥S,
      finrank (ZMod p) (continuousH1 (extArithLoc S (Sum.inr q))
          (Rep.res (extArithLoc S (Sum.inr q)) M))
        = finrank (ZMod p) (Rep.res (extArithLoc S (Sum.inr q)) M).ρ.invariants
          + finrank (ZMod p) ((Rep.res (extArithLoc S (Sum.inr q)) M).dualTwist
              ((cycloChar p).comp (primeLocalToGlobal q.1))).ρ.invariants
          + (if q = (⟨pPrime p, hpS⟩ : ↥S) then finrank (ZMod p) M else 0) := by
    intro q
    by_cases hq : q = (⟨pPrime p, hpS⟩ : ↥S)
    · subst hq
      rw [if_pos rfl]
      exact GreenbergWilesLegs.arm_local_euler_char_at_p S hpS M hsm
    · rw [if_neg hq]
      have hne : ((q : Nat.Primes) : ℕ) ≠ p := by
        intro hcoe
        apply hq
        apply Subtype.ext
        have : (q : Nat.Primes) = pPrime p := Subtype.ext hcoe
        exact this
      simpa using GreenbergWilesLegs.arm_local_euler_char_ne_p S M hsm q hne
  have hsum_EP : (∑ q : ↥S, finrank (ZMod p) (continuousH1 (extArithLoc S (Sum.inr q))
        (Rep.res (extArithLoc S (Sum.inr q)) M)))
      = (∑ q : ↥S, finrank (ZMod p) (Rep.res (extArithLoc S (Sum.inr q)) M).ρ.invariants)
        + (∑ q : ↥S, finrank (ZMod p) ((Rep.res (extArithLoc S (Sum.inr q)) M).dualTwist
            ((cycloChar p).comp (primeLocalToGlobal q.1))).ρ.invariants)
        + finrank (ZMod p) M := by
    rw [Finset.sum_congr rfl fun q _ => hEP q]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_ite_eq' Finset.univ (⟨pPrime p, hpS⟩ : ↥S) (fun _ => finrank (ZMod p) M)]
    simp
  have hsum_e8 : (∑ q : ↥S, finrank (ZMod p) (continuousH1 (extArithLoc S (Sum.inr q))
        (Rep.res (extArithLoc S (Sum.inr q)) M)))
      = ∑ q : ↥S, finrank (ZMod p) (continuousH1 (extArithLoc S (Sum.inr q))
          (Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p)))) :=
    Finset.sum_congr rfl fun q _ => e8 q
  omega

end S_groupCohomology_greenbergWilesLeAdm_extArithLoc_of_isTheta1_eval_of_ne_two
end P2MW
export P2MW.S_groupCohomology_greenbergWilesLeAdm_extArithLoc_of_isTheta1_eval_of_ne_two (solution)
