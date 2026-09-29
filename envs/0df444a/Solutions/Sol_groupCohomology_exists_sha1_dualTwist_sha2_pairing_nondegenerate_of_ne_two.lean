-- Prove2me | solution 1 for groupCohomology.exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/11dd292b-befb-5070-b99a-720e07ff4546

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousDuality
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_GroupCohomology_GlobalBridge
import Definitions.Def_GroupCohomology_LevelQuotient
import Definitions.Def_GroupCohomology_RelationHomDefect
import Definitions.Def_GroupCohomology_RelationModule
import Definitions.Def_GroupCohomology_RelationModuleRes
import Definitions.Def_GroupCohomology_RepImage
import Definitions.Def_GroupCohomology_RepToIntRep
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_M4aHerbrand_SIdeleClassTower
import Definitions.Def_NumberField_InfinitePlaceTransport
import Definitions.Def_NumberField_SArchIdeleModule
import Definitions.Def_NumberField_SUnitsModule
import Theorems.Thm_GroupCohomology_RepImage_seq_shortExact
import Theorems.Thm_GroupCohomology_RepPi_forall_exists_comp_proj_and_iff_exists_eq_comp_of_coind
import Theorems.Thm_GroupCohomology_RepPi_map_ihom_proj_one_injective_and_surjective
import Theorems.Thm_IntermediateField_adjoin_isUnramifiedOutside_of_isPrimitiveRoot_pow
import Theorems.Thm_IntermediateField_exists_normal_isUnramifiedOutside_of_le
import Theorems.Thm_M4aHerbrand_IdeleGaloisDescent_stabilizesUnitIdeles_placesOverPrimes
import Theorems.Thm_M4aHerbrand_bijective_groupCohomology_map_toSIdeleClass
import Theorems.Thm_M4aHerbrand_exists_adeleBaseChange_invariant_groupCohomology_ideleClassGroup_map_eq_of_invariant
import Theorems.Thm_M4aHerbrand_exists_fundamentalClass_sIdeleClassGroup
import Theorems.Thm_M4aHerbrand_exists_hom_adicCompletion_res_decomp_ideles_apply
import Theorems.Thm_M4aHerbrand_exists_invariant_groupCohomology_ideleClassGroup_forall_comp_eq_index_smul_of_ne_two
import Theorems.Thm_M4aHerbrand_exists_level_forall_relationHom_sIdeleClassGroup_extends_or_map_delta_ne_zero
import Theorems.Thm_M4aHerbrand_nonempty_ideleGaloisDescent
import Theorems.Thm_NumberField_AdeleRing_finiteIndex_principalIdeles_sup_unitIdelesOutside
import Theorems.Thm_NumberField_InfPlaceDecomp_exists_isLocalBridge1_archimedean
import Theorems.Thm_NumberField_InfPlaceDecomp_exists_isLocalBridge2_archimedean
import Theorems.Thm_NumberField_InfPlaceDecomp_exists_restrictNormalHom_conj_complexConjugation_mem_decomp
import Theorems.Thm_NumberField_InfPlaceDecomp_localBridge_hypotheses_archimedean
import Theorems.Thm_NumberField_PlaceDecomp_exists_isLocalBridge1_padicAlgCl
import Theorems.Thm_NumberField_PlaceDecomp_exists_ringHom_adicCompletion_padicAlgCl_extends_padicEmbedding
import Theorems.Thm_NumberField_PlaceDecomp_exists_unit_inv_map_delta_res_eq_theta_localBridge
import Theorems.Thm_NumberField_PlaceDecomp_exists_unit_inv_map_delta_res_eq_theta_localBridge_primary
import Theorems.Thm_NumberField_PlaceDecomp_localBridge_hypotheses_padicAlgCl
import Theorems.Thm_NumberField_PlaceTransport_orbit_eq_setOf_under_eq
import Theorems.Thm_NumberField_PlaceTransport_stabilizer_eq_decomp
import Theorems.Thm_NumberField_SArchIdele_existsUnique_hom_res_obj_comp_toSIdele_eq
import Theorems.Thm_NumberField_SArchIdele_toSIdeleClass_mk_comp_diagS_eq_one_and_exists_of_eq_one
import Theorems.Thm_NumberField_SIdele_exists_addMonoidHom_obj_adeleRing_units_apply
import Theorems.Thm_NumberField_SUnits_exists_ihom_extension_fixed_of_sLevel_of_injective
import Theorems.Thm_NumberField_SUnits_exists_isGlobalBridge2_apply_eq_continuousH2Spi_of_forall_mul_eq
import Theorems.Thm_NumberField_SUnits_exists_level_forall_map_extInflR_eq_zero_of_isGlobalBridge2_apply_eq_zero
import Theorems.Thm_NumberField_SUnits_isGlobalBridge2_apply_inflation_eq
import Theorems.Thm_NumberField_SUnits_locRes2S_isGlobalBridge2_apply_eq_of_finite
import Theorems.Thm_NumberField_exists_le_isGalois_forall_mem_range_sup_unitIdelesOutside_of_pow_mem
import Theorems.Thm_NumberField_ramificationIdx_span_eq_one_of_forall_liesOverPrime_inertiaSubgroupIn_le_fixingSubgroup
import Theorems.Thm_Rep_card_smul_eq_zero_of_tateCohomology
import Theorems.Thm_Rep_delta_hom_comp_eq_zero
import Theorems.Thm_Rep_dualTwist_cycloChar_smooth
import Theorems.Thm_Rep_dualTwist_cycloChar_unramifiedOutside
import Theorems.Thm_Rep_exists_delta_hom_eq_of_map_ihom_map_eq_zero
import Theorems.Thm_Rep_exists_eq_comp_of_delta_hom_eq_zero
import Theorems.Thm_Rep_exists_hom_relationModuleInt_forall_map_delta_eq
import Theorems.Thm_Rep_exists_preIota_eq_map_extInflR_zero_of_exists_preIota_eq_of_pit
import Theorems.Thm_Rep_exists_resMap_comp_eq_comp_add_iota_comp_of_pit
import Theorems.Thm_Rep_isEquivariantBilinear_eval_dualTwist
import Theorems.Thm_Rep_map_delta_resMap_comp_eq_map_map_delta
import Theorems.Thm_Rep_moduleFree_relationCarrier
import Theorems.Thm_Rep_nonempty_res_free_iso_free
import Theorems.Thm_Rep_relationSeqInt_shortExact
import Theorems.Thm_Rep_shortExact_map_ihom_of_free
import Theorems.Thm_TWNum_finiteDimensional_continuousH2S
import Theorems.Thm_groupCohomology_alpha1Read_comp_eq_sum_theta_of_forall_local
import Theorems.Thm_groupCohomology_bijective_of_isTheta1_localInv_extArithLoc
import Theorems.Thm_groupCohomology_exists_alpha1Read_of_injective_invariant
import Theorems.Thm_groupCohomology_exists_corestriction_comp_res_eq_index_nsmul
import Theorems.Thm_groupCohomology_exists_inflate_H1_injective_range_iff_split
import Theorems.Thm_groupCohomology_exists_isGalois_forall_mem_continuousH1S_exists_cocyclesOne
import Theorems.Thm_groupCohomology_exists_isGlobalBridge2
import Theorems.Thm_groupCohomology_exists_isLocalBridge2
import Theorems.Thm_groupCohomology_exists_isUnramifiedOutside_forall_apply_eq_one_of_smooth
import Theorems.Thm_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_assembly
import Theorems.Thm_groupCohomology_exists_theta1
import Theorems.Thm_groupCohomology_finiteDimensional_continuousH1S
import Theorems.Thm_groupCohomology_finrank_submodule_res_extArithLoc_archSlot_eq_zero
import Theorems.Thm_groupCohomology_isLocalBridge2_injective
import Theorems.Thm_groupCohomology_locRes_mem_continuousH1_of_mem_continuousH1S
import Theorems.Thm_groupCohomology_map_delta_eq_delta_map
import Theorems.Thm_groupCohomology_map_resIhom_comp_ihom_map_counit_one_bijective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two
p2m_attr_erase "instance" "FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing"
p2m_attr_erase "instance" "M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion NumberField.AdelicHaar.locallyCompactSpace_adeleRing NumberField.AdelicHaar.finite_residueField_adicCompletionIntegers NumberField.AdelicHaar.locallyCompactSpace_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_finiteAdeleRing NumberField.AdelicHaar.compactSpace_adicCompletionIntegers NumberField.AdelicHaar.t2Space_finiteAdeleRing NumberField.AdelicHaar.t2Space_matrix_adeleRing NumberField.AdelicHaar.t2Space_adeleRing NumberField.AdelicHaar.fact_isOpen_adicCompletionIntegers NumberField.AdelicHaar.t2Space_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_matrix_adeleRing NumberField.AdelicHaar.t2Space_infiniteAdeleRing NumberField.AdelicHaar.properSpace_adicCompletion M4aHerbrand.Bridge.instT2SpaceAdeleRing ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite Deep.NTSupply.instNormalRayClassSubgroup instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal groupCohomology.Kummer.instMulDistribMulActionRootsOfUnity NumberField.LevelArith.instCommGroupUnitsModPow"
p2m_attr_erase "simp" "M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq M4aHerbrand.Bridge.finiteConorm_apply SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply"
p2m_attr_erase "simp" "SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply"
p2m_attr_erase "simp" "Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply Representation.TateResCor.cosetDecomp_apply Rep.coe_tateHneg1Res_apply Representation.TateResCor.coe_tateHneg1Cores_apply Representation.TateResCor.tateH0Res_mk Rep.coe_tateHneg1Cores_apply Rep.tateH0Res_mk Representation.TateResCor.coe_cosetNormInvariants_apply Rep.tateH0Cores_mk Representation.TateResCor.coinvariantsCores_mk Representation.TateResCor.coinvariantsTransfer_mk Representation.TateResCor.tateH0Cores_mk Representation.TateResCor.coe_tateHneg1Res_apply IsLocalRing.principalUnits_zero LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b"
p2m_attr_erase "simp" "AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq Rep.splittingShortComplex_X₃ Rep.splittingShortComplex_X₁ Rep.splittingShortComplex_X₂ Rep.splittingShortComplex_f Rep.augShortComplex_f Rep.augShortComplex_X₃ Rep.cocycleTwist_single Rep.augShortComplex_X₂ Rep.splittingModuleι_hom_apply Rep.augShortComplex_X₁ Rep.splittingShortComplex_g Rep.augShortComplex_g Rep.splittingModuleπ_hom_apply Rep.coe_dimShiftDownObjMap_apply groupCohomology.Kummer.coe_kummerCocycleRoots groupCohomology.Kummer.mem_powerSubgroup_iff groupCohomology.Kummer.val_smul_units groupCohomology.Kummer.kummerHom_apply groupCohomology.Kummer.coe_smul_rootsOfUnity groupCohomology.coe_continuousH1SrMap_apply groupCohomology.continuousH2SrMap_continuousH2Srπ groupCohomology.coe_levelCocyclesSr₂Map NumberField.LevelArith.coe_levelFieldEquiv NumberField.LevelArith.modP_apply_mk NumberField.LevelArith.coe_levelFieldEquiv_symm NumberField.LevelArith.torsionP_apply_coe NumberField.LevelArith.repTorsionPMap_hom_apply_coe NumberField.LevelArith.toZMod_apply"
p2m_attr_erase "simp" "NumberField.LevelArith.repModPMap_hom_mk groupCohomology.continuousH2Inflation_H2π groupCohomology.levelInflate₂_apply groupCohomology.coe_levelInflateCocycles₂ groupCohomology.levelInflate₁_apply NumberField.LevelArith.smul_mk NumberField.LevelArith.selmerRepInt_ρ_apply NumberField.LevelArith.selmerRepField_ρ_apply NumberField.LevelArith.unitsModPowMap_mk Rep.quotientRightTranslation_hom_single Rep.quotientRightTranslationTwist_hom_apply"

set_option autoImplicit false
open CategoryTheory IsDedekindDomain NumberField

namespace Reduce95

section places

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

noncomputable abbrev placeOf (q : Nat.Primes) : HeightOneSpectrum (𝓞 ℚ) := Rat.HeightOneSpectrum.primesEquiv.symm q

theorem natCast_mem_asIdeal_iff (v : HeightOneSpectrum (𝓞 ℚ)) (p : Nat.Primes) :
    ((p : ℕ) : 𝓞 ℚ) ∈ v.asIdeal ↔ Rat.HeightOneSpectrum.primesEquiv v = p := by
  have h1 : ((p : ℕ) : 𝓞 ℚ) ∈ v.asIdeal ↔ Rat.HeightOneSpectrum.natGenerator v ∣ (p : ℕ) := by
    rw [Rat.HeightOneSpectrum.natGenerator_dvd_iff, ← map_natCast (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) (p : ℕ),
      Ideal.apply_mem_of_equiv_iff]
  rw [h1, Nat.prime_dvd_prime_iff_eq (Rat.HeightOneSpectrum.prime_natGenerator v) p.2]
  constructor
  · intro h; exact Subtype.ext h
  · intro h; exact congrArg Subtype.val h

theorem natCast_mem_asIdeal_placeOf (q : Nat.Primes) : ((q : ℕ) : 𝓞 ℚ) ∈ (placeOf q).asIdeal := by
  rw [natCast_mem_asIdeal_iff, placeOf, Equiv.apply_symm_apply]

noncomputable def Sq (S : Finset Nat.Primes) : Finset (HeightOneSpectrum (𝓞 ℚ)) :=
  S.map Rat.HeightOneSpectrum.primesEquiv.symm.toEmbedding

theorem mem_Sq_iff (S : Finset Nat.Primes) (v : HeightOneSpectrum (𝓞 ℚ)) :
    v ∈ Sq S ↔ Rat.HeightOneSpectrum.primesEquiv v ∈ S := by
  simp only [Sq, Finset.mem_map_equiv, Equiv.symm_symm]

theorem coe_Sq (S : Finset Nat.Primes) : (↑(Sq S) : Set (HeightOneSpectrum (𝓞 ℚ))) = NumberField.placesOverPrimes ℚ (↑S : Set Nat.Primes) := by
  ext v
  rw [Finset.mem_coe, mem_Sq_iff, NumberField.mem_placesOverPrimes_iff]
  constructor
  · intro h; exact ⟨_, h, (natCast_mem_asIdeal_iff v _).2 rfl⟩
  · rintro ⟨p, hp, hpv⟩; rwa [(natCast_mem_asIdeal_iff v p).1 hpv]

noncomputable def eS (S : Finset Nat.Primes) : ↥S ≃ {v // v ∈ Sq S} where
  toFun q := ⟨placeOf q.1, (mem_Sq_iff S _).2 (by rw [placeOf, Equiv.apply_symm_apply]; exact q.2)⟩
  invFun v := ⟨Rat.HeightOneSpectrum.primesEquiv v.1, (mem_Sq_iff S v.1).1 v.2⟩
  left_inv q := Subtype.ext (by simp [placeOf])
  right_inv v := Subtype.ext (by simp [placeOf])

@[scoped simp] theorem eS_apply_coe (S : Finset Nat.Primes) (q : ↥S) : ((eS S q : {v // v ∈ Sq S}) : HeightOneSpectrum (𝓞 ℚ)) = placeOf q.1 := rfl

noncomputable def eIdx (S : Finset Nat.Primes) : ExtCitation.extArithIndex S ≃ NumberField.SArchIdele.Index ℚ (Sq S) :=
  (Equiv.sumComm Unit ↥S).trans (Equiv.sumCongr (eS S) (Equiv.ofUnique Unit (InfinitePlace ℚ)))

@[scoped simp] theorem eIdx_inr (S : Finset Nat.Primes) (q : ↥S) : eIdx S (Sum.inr q) = Sum.inl (eS S q) := rfl
@[scoped simp] theorem eIdx_inl (S : Finset Nat.Primes) (u : Unit) : eIdx S (Sum.inl u) = Sum.inr default := rfl

end places

section sunits

variable (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F] (Sℚ : Finset (HeightOneSpectrum (𝓞 ℚ)))

noncomputable def iotaE : NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ →+ Additive (AlgebraicClosure ℚ)ˣ :=
  (MonoidHom.toAdditive (Units.map (algebraMap ↥F (AlgebraicClosure ℚ) : ↥F →* AlgebraicClosure ℚ))).comp
    (AddSubgroup.subtype (Subgroup.toAddSubgroup (NumberField.SUnits.sUnits ℚ ↥F Sℚ)))

theorem toMul_iotaE (x : NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ) :
    Additive.toMul (iotaE F Sℚ x) = Units.map (algebraMap ↥F (AlgebraicClosure ℚ) : ↥F →* AlgebraicClosure ℚ) (NumberField.SUnits.val ℚ ↥F Sℚ x) := rfl

theorem iotaE_injective : Function.Injective (iotaE F Sℚ) := by
  intro x y h
  have h' := congrArg Additive.toMul h
  rw [toMul_iotaE, toMul_iotaE] at h'
  have h'' : NumberField.SUnits.val ℚ ↥F Sℚ x = NumberField.SUnits.val ℚ ↥F Sℚ y := by
    apply Units.ext
    have := congrArg (fun u : (AlgebraicClosure ℚ)ˣ => (u : AlgebraicClosure ℚ)) h'
    simpa using this
  exact Subtype.ext (congrArg Additive.ofMul h'')

theorem iotaE_equivariant (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ) :
    iotaE F Sℚ ((NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ).ρ (AlgEquiv.restrictNormalHom ↥F γ) x) =
      (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)).ρ γ (iotaE F Sℚ x) := by
  apply congrArg Additive.ofMul
  apply Units.ext
  change algebraMap ↥F (AlgebraicClosure ℚ) ((AlgEquiv.restrictNormalHom ↥F γ) (NumberField.SUnits.val ℚ ↥F Sℚ x : ↥F)) =
    γ (algebraMap ↥F (AlgebraicClosure ℚ) (NumberField.SUnits.val ℚ ↥F Sℚ x : ↥F))
  exact AlgEquiv.restrictNormal_commutes γ ↥F _

end sunits

end Reduce95
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

namespace Reduce95
open M4aHerbrand

section idele
open scoped RestrictedProduct Classical

variable (F : Type) [Field F] [NumberField F]

noncomputable def finSingle (w : HeightOneSpectrum (𝓞 F)) : w.adicCompletion F →* FiniteAdeleRing (𝓞 F) F where
  toFun x := (RestrictedProduct.mulSingle (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletionIntegers F) w x :
    Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, v.adicCompletionIntegers F])
  map_one' := RestrictedProduct.mulSingle_one _ w
  map_mul' x y := RestrictedProduct.mulSingle_mul _ w x y

theorem finSingle_apply_same (w : HeightOneSpectrum (𝓞 F)) (x : w.adicCompletion F) : finSingle F w x w = x :=
  RestrictedProduct.mulSingle_eq_same _ w x

theorem finSingle_apply_of_ne (w w' : HeightOneSpectrum (𝓞 F)) (h : w' ≠ w) (x : w.adicCompletion F) : finSingle F w x w' = 1 :=
  RestrictedProduct.mulSingle_eq_of_ne _ x h

noncomputable def adeleSingle (w : HeightOneSpectrum (𝓞 F)) : w.adicCompletion F →* AdeleRing (𝓞 F) F where
  toFun x := (show AdeleRing (𝓞 F) F from ((1 : InfiniteAdeleRing F), finSingle F w x))
  map_one' := by rw [map_one]; rfl
  map_mul' x y := by
    rw [map_mul]
    change ((1 : InfiniteAdeleRing F), finSingle F w x * finSingle F w y) =
      (((1 : InfiniteAdeleRing F), finSingle F w x) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F) * ((1 : InfiniteAdeleRing F), finSingle F w y)
    rw [Prod.mk_mul_mk, one_mul]

noncomputable def iotaW (w : HeightOneSpectrum (𝓞 F)) : (w.adicCompletion F)ˣ →* (AdeleRing (𝓞 F) F)ˣ := Units.map (adeleSingle F w)

theorem iotaW_spec (w : HeightOneSpectrum (𝓞 F)) (x : (w.adicCompletion F)ˣ) :
    finPart w (iotaW F w x) = x ∧ (∀ w' : HeightOneSpectrum (𝓞 F), w' ≠ w → finPart w' (iotaW F w x) = 1) ∧ infPart (iotaW F w x) = 1 := by
  refine ⟨Units.ext ?_, fun w' hw' => Units.ext ?_, Units.ext ?_⟩
  · exact finSingle_apply_same F w x
  · exact finSingle_apply_of_ne F w w' hw' x
  · rfl

theorem coe_iotaW_fst (w : HeightOneSpectrum (𝓞 F)) (x : (w.adicCompletion F)ˣ) : ((iotaW F w x : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 = 1 := rfl
theorem coe_iotaW_snd_apply (w : HeightOneSpectrum (𝓞 F)) (x : (w.adicCompletion F)ˣ) (w' : HeightOneSpectrum (𝓞 F)) :
    ((iotaW F w x : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 w' = finSingle F w x w' := rfl

theorem idele_ext {x y : (AdeleRing (𝓞 F) F)ˣ} (hinf : infPart x = infPart y) (hfin : ∀ w, finPart w x = finPart w y) : x = y := by
  apply Units.ext
  refine Prod.ext (congrArg Units.val hinf) ?_
  apply FiniteAdeleRing.ext
  intro w
  exact congrArg Units.val (hfin w)

end idele
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

section actions

variable (E F : Type) [Field E] [Field F] [NumberField F] [Algebra E F]

@[reducible] noncomputable def idelesAction (D : IdeleGaloisDescent (𝓞 F) E F) : MulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ :=
  MulDistribMulAction.compHom _ D.unitsAct

theorem idelesAction_smul (D : IdeleGaloisDescent (𝓞 F) E F) (g : F ≃ₐ[E] F) (x : (AdeleRing (𝓞 F) F)ˣ) :
    (letI := idelesAction E F D; g • x) = D.unitsAct g x := rfl

noncomputable def idelesToClassRepHom (D : IdeleGaloisDescent (𝓞 F) E F) :
    letI := idelesAction E F D; letI := D.classMulDistribMulAction;
    Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ ⟶ Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F) :=
  letI := idelesAction E F D; letI := D.classMulDistribMulAction;
  repHomOfMulEquivariant (QuotientGroup.mk' (principalIdeles (𝓞 F) F)) fun g x => rfl

end actions
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

end Reduce95
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

namespace Reduce95
open ExtCitation GroupCohomology

section reppi
universe u
variable {k G : Type u} [CommRing k] [Group G] {ι : Type u} (Fm : ι → Rep.{u} k G)

open scoped Classical in

noncomputable def incl (i : ι) : Fm i ⟶ RepPi.obj Fm :=
  RepPi.lift Fm fun j => if h : i = j then eqToHom (congrArg Fm h) else 0

theorem incl_proj_self (i : ι) : incl Fm i ≫ RepPi.proj Fm i = 𝟙 (Fm i) := by
  rw [incl, RepPi.lift_proj, dif_pos rfl]; rfl

theorem incl_proj_of_ne {i j : ι} (h : i ≠ j) : incl Fm i ≫ RepPi.proj Fm j = 0 := by
  rw [incl, RepPi.lift_proj, dif_neg h]

theorem proj_eqToHom {i j : ι} (h : i = j) : RepPi.proj Fm i ≫ eqToHom (congrArg Fm h) = RepPi.proj Fm j := by
  subst h; simp

theorem eqToHom_incl {i j : ι} (h : i = j) : eqToHom (congrArg Fm h) ≫ incl Fm j = incl Fm i := by
  subst h; simp

theorem sum_proj_incl [Fintype ι] : ∑ i, RepPi.proj Fm i ≫ incl Fm i = 𝟙 (RepPi.obj Fm) := by
  classical
  apply RepPi.hom_ext
  intro j
  rw [Preadditive.sum_comp, Category.id_comp]
  rw [Finset.sum_eq_single j]
  · rw [Category.assoc, incl_proj_self, Category.comp_id]
  · intro i _ hij; rw [Category.assoc, incl_proj_of_ne Fm hij, Limits.comp_zero]
  · intro h; exact absurd (Finset.mem_univ j) h

end reppi
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

section reindex
open scoped NumberField.PlaceDecomp NumberField.InfPlaceDecomp

variable (S : Finset Nat.Primes) (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F]

noncomputable def Dv : extArithIndex S → Subgroup (↥F ≃ₐ[ℚ] ↥F)
  | Sum.inl _ => NumberField.InfPlaceDecomp.decomp ℚ ↥F (NumberField.ArchIdele.above ℚ ↥F default)
  | Sum.inr q => NumberField.FiniteSIdele.D ℚ ↥F (placeOf q.1)

noncomputable def Yv : ∀ v : extArithIndex S, Rep ℤ ↥(Dv S F v)
  | Sum.inl _ => NumberField.InfPlaceDecomp.localUnits ℚ ↥F (NumberField.ArchIdele.above ℚ ↥F default)
  | Sum.inr q => NumberField.FiniteSIdele.localUnits ℚ ↥F (placeOf q.1)

noncomputable abbrev J0fam : extArithIndex S → Rep ℤ (↥F ≃ₐ[ℚ] ↥F) := fun v => Rep.coind (Dv S F v).subtype (Yv S F v)

theorem J0fam_eq_fibre (v : extArithIndex S) : J0fam S F v = NumberField.SArchIdele.fibre ℚ ↥F (Sq S) (eIdx S v) := by
  rcases v with u | q
  · rfl
  · rfl

noncomputable def rHom : NumberField.SArchIdele.obj ℚ ↥F (Sq S) ⟶ RepPi.obj (J0fam S F) :=
  RepPi.lift (J0fam S F) fun v => NumberField.SArchIdele.proj ℚ ↥F (Sq S) (eIdx S v) ≫ eqToHom (J0fam_eq_fibre S F v).symm

theorem rHom_proj (v : extArithIndex S) :
    rHom S F ≫ RepPi.proj (J0fam S F) v = NumberField.SArchIdele.proj ℚ ↥F (Sq S) (eIdx S v) ≫ eqToHom (J0fam_eq_fibre S F v).symm :=
  RepPi.lift_proj _ _ v

theorem rHom_proj_inr (q : ↥S) :
    rHom S F ≫ RepPi.proj (J0fam S F) (Sum.inr q) = (NumberField.SArchIdele.proj ℚ ↥F (Sq S) (Sum.inl (eS S q)) : _ ⟶ J0fam S F (Sum.inr q)) := by
  rw [rHom_proj]
  exact (congrArg (NumberField.SArchIdele.proj ℚ ↥F (Sq S) (Sum.inl (eS S q)) ≫ ·) (eqToHom_refl _ _)).trans (Category.comp_id _)

theorem rHom_proj_inl (u : Unit) :
    rHom S F ≫ RepPi.proj (J0fam S F) (Sum.inl u) = (NumberField.SArchIdele.proj ℚ ↥F (Sq S) (Sum.inr default) : _ ⟶ J0fam S F (Sum.inl u)) := by
  rw [rHom_proj]
  exact (congrArg (NumberField.SArchIdele.proj ℚ ↥F (Sq S) (Sum.inr default) ≫ ·) (eqToHom_refl _ _)).trans (Category.comp_id _)

theorem rHom_hom_apply_inr (x : NumberField.SArchIdele.obj ℚ ↥F (Sq S)) (q : ↥S) :
    (rHom S F).hom x (Sum.inr q) = (x (Sum.inl (eS S q)) : J0fam S F (Sum.inr q)) := by
  have := congrArg (fun φ => φ.hom x) (rHom_proj_inr S F q)
  exact this

theorem rHom_hom_apply_inl (x : NumberField.SArchIdele.obj ℚ ↥F (Sq S)) (u : Unit) :
    (rHom S F).hom x (Sum.inl u) = (x (Sum.inr default) : J0fam S F (Sum.inl u)) := by
  have := congrArg (fun φ => φ.hom x) (rHom_proj_inl S F u)
  exact this

noncomputable def rInv : RepPi.obj (J0fam S F) ⟶ NumberField.SArchIdele.obj ℚ ↥F (Sq S) :=
  RepPi.lift _ fun i => RepPi.proj (J0fam S F) ((eIdx S).symm i) ≫
    eqToHom ((J0fam_eq_fibre S F ((eIdx S).symm i)).trans (congrArg (NumberField.SArchIdele.fibre ℚ ↥F (Sq S)) ((eIdx S).apply_symm_apply i)))

theorem rHom_rInv : rHom S F ≫ rInv S F = 𝟙 _ := by
  apply RepPi.hom_ext; intro i
  rw [Category.id_comp, rInv, Category.assoc, RepPi.lift_proj, ← Category.assoc, rHom_proj, Category.assoc, eqToHom_trans]
  exact proj_eqToHom (NumberField.SArchIdele.fibre ℚ ↥F (Sq S)) ((eIdx S).apply_symm_apply i)

theorem rInv_rHom : rInv S F ≫ rHom S F = 𝟙 _ := by
  apply RepPi.hom_ext; intro v
  rw [Category.id_comp, Category.assoc, rHom_proj, ← Category.assoc, rInv, RepPi.lift_proj, Category.assoc, eqToHom_trans]
  have h := (eIdx S).symm_apply_apply v
  exact proj_eqToHom (J0fam S F) h

end reindex
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

end Reduce95
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

namespace Reduce95
open Rep

universe u
variable {k G : Type u} [CommRing k] [Group G] {S : Subgroup G} [DecidableRel (QuotientGroup.rightRel S)] [S.FiniteIndex]

theorem coind_homEquiv_hom_apply (A : Rep.{u} k S) (B : Rep.{u} k G) (f : coind S.subtype A ⟶ B) (a : A) :
    ((Rep.coindResAdjunction k S).homEquiv A B f).hom a = f.hom ((Rep.indCoindIso A).hom.hom (Representation.IndV.mk S.subtype A.ρ 1 a)) := by
  rw [Rep.coindResAdjunction_homEquiv_apply]
  rfl

theorem indCoindIso_hom_mk_one_apply (A : Rep.{u} k S) (a : A) (g : G) :
    ((Rep.indCoindIso A).hom.hom (Representation.IndV.mk S.subtype A.ρ 1 a)).1 g = Rep.indToCoindAux A 1 a g := by
  have h1 : (Rep.indCoindIso A).hom.hom (Representation.IndV.mk S.subtype A.ρ 1 a) = Rep.indToCoind A (Representation.IndV.mk S.subtype A.ρ 1 a) := by
    rw [← Rep.indCoindIso_hom_hom_toLinearMap A]; rfl
  rw [h1]
  simp [Representation.IndV.mk]

theorem indToCoindAux_one_of_mem (A : Rep.{u} k S) (a : A) (g : G) (hg : g ∈ S) :
    Rep.indToCoindAux A 1 a g = A.ρ ⟨g, hg⟩ a := by
  have := Rep.indToCoindAux_mul_snd (A := A) (1 : G) 1 a ⟨g, hg⟩
  simpa using this

theorem indToCoindAux_one_of_not_mem (A : Rep.{u} k S) (a : A) (g : G) (hg : g ∉ S) :
    Rep.indToCoindAux A 1 a g = 0 := by
  apply Rep.indToCoindAux_of_not_rel
  rintro ⟨s, hs⟩
  apply hg
  have : (s : G) * 1 = g := hs
  rw [mul_one] at this
  rw [← this]; exact s.2

end Reduce95
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

namespace Reduce95
open ExtCitation GroupCohomology M4aHerbrand
open scoped NumberField.PlaceDecomp NumberField.InfPlaceDecomp

section tset
variable (S : Finset Nat.Primes) (F : Type) [Field F] [NumberField F]

theorem under_mem_Sq_iff (w : HeightOneSpectrum (𝓞 F)) :
    w.under (𝓞 ℚ) ∈ Sq S ↔ w ∈ NumberField.placesOverPrimes F (↑S : Set Nat.Primes) := by
  rw [mem_Sq_iff, NumberField.mem_placesOverPrimes_iff]
  constructor
  · intro h
    refine ⟨_, h, ?_⟩
    have h2 := (natCast_mem_asIdeal_iff (w.under (𝓞 ℚ)) (Rat.HeightOneSpectrum.primesEquiv (w.under (𝓞 ℚ)))).2 rfl
    have h3 : (algebraMap (𝓞 ℚ) (𝓞 F)) ((Rat.HeightOneSpectrum.primesEquiv (w.under (𝓞 ℚ)) : ℕ) : 𝓞 ℚ) ∈ w.asIdeal := h2
    rwa [map_natCast] at h3
  · rintro ⟨p, hp, hpw⟩
    have h3 : ((p : ℕ) : 𝓞 ℚ) ∈ (w.under (𝓞 ℚ)).asIdeal := by
      show (algebraMap (𝓞 ℚ) (𝓞 F)) ((p : ℕ) : 𝓞 ℚ) ∈ w.asIdeal
      rwa [map_natCast]
    rwa [(natCast_mem_asIdeal_iff _ p).1 h3]

theorem setOf_under_mem_Sq : {w : HeightOneSpectrum (𝓞 F) | w.under (𝓞 ℚ) ∈ Sq S} = NumberField.placesOverPrimes F (↑S : Set Nat.Primes) :=
  Set.ext fun w => under_mem_Sq_iff S F w

end tset
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

attribute [scoped instance 10] AddCommGroup.toIntModule

section classmaps

variable (F : Type) [Field F] [NumberField F] (Sℚ : Finset (HeightOneSpectrum (𝓞 ℚ)))
  (D : IdeleGaloisDescent (𝓞 F) ℚ F) (T : Set (HeightOneSpectrum (𝓞 F)))
  [MulDistribMulAction (F ≃ₐ[ℚ] F) (AdeleRing (𝓞 F) F)ˣ]
  [MulDistribMulAction (F ≃ₐ[ℚ] F) (IdeleClassGroup (𝓞 F) F)]
  [MulDistribMulAction (F ≃ₐ[ℚ] F) (SIdeleClassGroup (𝓞 F) F T)]
  (hactI : ∀ (g : F ≃ₐ[ℚ] F) (x : (AdeleRing (𝓞 F) F)ˣ), g • x = D.unitsAct g x)
  (hact : ∀ (g : F ≃ₐ[ℚ] F) (c : IdeleClassGroup (𝓞 F) F), g • c = D.classAct g c)
  (hactS : ∀ (g : F ≃ₐ[ℚ] F) (c : IdeleClassGroup (𝓞 F) F), g • toSIdeleClass (𝓞 F) F T c = toSIdeleClass (𝓞 F) F T (D.classAct g c))
  (Φ : NumberField.SIdele.obj ℚ F Sℚ →+ Additive (AdeleRing (𝓞 F) F)ˣ)
  (hΦeq : ∀ (g : F ≃ₐ[ℚ] F) (x : NumberField.SIdele.obj ℚ F Sℚ),
    Φ ((NumberField.SIdele.obj ℚ F Sℚ).ρ g x) = Additive.ofMul (D.unitsAct g (Additive.toMul (Φ x))))

noncomputable def qI : Rep.ofMulDistribMulAction (F ≃ₐ[ℚ] F) (AdeleRing (𝓞 F) F)ˣ ⟶ Rep.ofMulDistribMulAction (F ≃ₐ[ℚ] F) (IdeleClassGroup (𝓞 F) F) :=
  repHomOfMulEquivariant (QuotientGroup.mk' (principalIdeles (𝓞 F) F)) fun g x => by
    rw [hact, hactI]; rfl

include hact hactS in

noncomputable def qS : Rep.ofMulDistribMulAction (F ≃ₐ[ℚ] F) (IdeleClassGroup (𝓞 F) F) ⟶ Rep.ofMulDistribMulAction (F ≃ₐ[ℚ] F) (SIdeleClassGroup (𝓞 F) F T) :=
  toSIdeleClassRepHom T (toSIdeleClass_smul_of_descent D T hact hactS)

noncomputable def LIlin : ↥(NumberField.SArchIdele.obj ℚ F Sℚ) →ₗ[ℤ] ↥(Rep.ofMulDistribMulAction (F ≃ₐ[ℚ] F) (AdeleRing (𝓞 F) F)ˣ) :=
  LinearMap.mk
    ⟨fun x => Φ ((NumberField.SArchIdele.toSIdele ℚ F Sℚ).hom x), fun x y =>
      (congrArg Φ ((NumberField.SArchIdele.toSIdele ℚ F Sℚ).hom.toLinearMap.map_add x y)).trans (map_add Φ _ _)⟩
    (fun n x => by
      dsimp only [RingHom.id_apply]
      have h := (NumberField.SArchIdele.toSIdele ℚ F Sℚ).hom.toLinearMap.map_smul n x
      rw [Representation.IntertwiningMap.coe_toLinearMap] at h
      rw [h]
      exact (congrArg Φ (int_smul_eq_zsmul (NumberField.SIdele.obj ℚ F Sℚ).hV2 n _)).trans (map_zsmul Φ n _))

theorem LIlin_apply (x : NumberField.SArchIdele.obj ℚ F Sℚ) : LIlin F Sℚ Φ x = Φ ((NumberField.SArchIdele.toSIdele ℚ F Sℚ).hom x) := rfl

noncomputable def LI : NumberField.SArchIdele.obj ℚ F Sℚ ⟶ Rep.ofMulDistribMulAction (F ≃ₐ[ℚ] F) (AdeleRing (𝓞 F) F)ˣ :=
  Rep.ofHom ⟨LIlin F Sℚ Φ, fun g => LinearMap.ext fun x => by
      change Φ ((NumberField.SArchIdele.toSIdele ℚ F Sℚ).hom ((NumberField.SArchIdele.obj ℚ F Sℚ).ρ g x)) =
        (Rep.ofMulDistribMulAction (F ≃ₐ[ℚ] F) (AdeleRing (𝓞 F) F)ˣ).ρ g (Φ ((NumberField.SArchIdele.toSIdele ℚ F Sℚ).hom x))
      rw [Rep.hom_comm_apply, hΦeq, Rep.ofMulDistribMulAction_ρ_apply_apply, hactI]⟩

theorem LI_hom_apply (x : NumberField.SArchIdele.obj ℚ F Sℚ) :
    (LI F Sℚ D hactI Φ hΦeq).hom x = Φ ((NumberField.SArchIdele.toSIdele ℚ F Sℚ).hom x) := rfl

noncomputable def LS : NumberField.SArchIdele.obj ℚ F Sℚ ⟶ Rep.ofMulDistribMulAction (F ≃ₐ[ℚ] F) (SIdeleClassGroup (𝓞 F) F T) :=
  LI F Sℚ D hactI Φ hΦeq ≫ qI F D hactI hact ≫ qS F D T hact hactS

theorem LS_hom_apply (x : NumberField.SArchIdele.obj ℚ F Sℚ) :
    (LS F Sℚ D T hactI hact hactS Φ hΦeq).hom x =
      Additive.ofMul (toSIdeleClass (𝓞 F) F T (QuotientGroup.mk (Additive.toMul (Φ ((NumberField.SArchIdele.toSIdele ℚ F Sℚ).hom x))))) := rfl

end classmaps
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

end Reduce95
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

namespace Reduce95
open ExtCitation GroupCohomology M4aHerbrand

section lams
open scoped Classical

variable (S : Finset Nat.Primes) (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F]
  {C : Rep ℤ (↥F ≃ₐ[ℚ] ↥F)} (L : NumberField.SArchIdele.obj ℚ ↥F (Sq S) ⟶ C)

scoped instance finiteIndex_Dv (v : extArithIndex S) : (Dv S F v).FiniteIndex := Subgroup.finiteIndex_of_finite

noncomputable def psiV (v : extArithIndex S) : J0fam S F v ⟶ C :=
  eqToHom (J0fam_eq_fibre S F v) ≫ incl (NumberField.SArchIdele.fibre ℚ ↥F (Sq S)) (eIdx S v) ≫ L

noncomputable def lamV (v : extArithIndex S) : Yv S F v ⟶ Rep.res (Dv S F v).subtype C :=
  (Rep.coindResAdjunction ℤ (Dv S F v)).homEquiv (Yv S F v) C (psiV S F L v)

noncomputable def lamJ0 : RepPi.obj (J0fam S F) ⟶ C :=
  ∑ v, RepPi.proj (J0fam S F) v ≫ ((Rep.coindResAdjunction ℤ (Dv S F v)).homEquiv (Yv S F v) C).symm (lamV S F L v)

theorem lamJ0_eq : lamJ0 S F L = ∑ v, RepPi.proj (J0fam S F) v ≫ psiV S F L v := by
  unfold lamJ0 lamV
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Equiv.symm_apply_apply]

theorem rHom_lamJ0 : rHom S F ≫ lamJ0 S F L = L := by
  rw [lamJ0_eq, Preadditive.comp_sum]
  have h1 : ∀ v, rHom S F ≫ RepPi.proj (J0fam S F) v ≫ psiV S F L v =
      NumberField.SArchIdele.proj ℚ ↥F (Sq S) (eIdx S v) ≫ incl (NumberField.SArchIdele.fibre ℚ ↥F (Sq S)) (eIdx S v) ≫ L := by
    intro v
    rw [← Category.assoc, rHom_proj, psiV, Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  simp_rw [h1]
  rw [Equiv.sum_comp (eIdx S) (fun i => NumberField.SArchIdele.proj ℚ ↥F (Sq S) i ≫ incl (NumberField.SArchIdele.fibre ℚ ↥F (Sq S)) i ≫ L)]
  simp_rw [← Category.assoc]
  rw [← Preadditive.sum_comp, sum_proj_incl, Category.id_comp]

end lams
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

end Reduce95
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

namespace Reduce95
open ExtCitation GroupCohomology M4aHerbrand

section seqEJY

variable (F : Type) [Field F] [NumberField F] (Sℚ : Finset (HeightOneSpectrum (𝓞 ℚ)))
  {C : Rep ℤ (F ≃ₐ[ℚ] F)} (L : NumberField.SArchIdele.obj ℚ F Sℚ ⟶ C)

theorem diagS_injective : Function.Injective (NumberField.SArchIdele.diagS ℚ F Sℚ).hom := by
  intro x y h
  have h1 := congrArg (fun z : NumberField.SArchIdele.obj ℚ F Sℚ => ((z (Sum.inr default) : NumberField.ArchIdele.fibre ℚ F default)).1 1) h
  dsimp only at h1
  rw [NumberField.SArchIdele.diagS_hom_apply_inr, NumberField.SArchIdele.diagS_hom_apply_inr,
    NumberField.SIdele.diagInf_hom_apply_apply, NumberField.SIdele.diagInf_hom_apply_apply, one_smul, one_smul] at h1
  have h2 := congrArg (fun u : ((NumberField.ArchIdele.above ℚ F default).Completion)ˣ => (u : (NumberField.ArchIdele.above ℚ F default).Completion)) (Additive.ofMul.injective h1)
  simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe] at h2
  have h3 : (NumberField.SUnits.val ℚ F Sℚ x : F) = NumberField.SUnits.val ℚ F Sℚ y := (NumberField.SIdele.locInf ℚ F default).injective h2
  exact Subtype.ext (congrArg Additive.ofMul (Units.ext h3))

variable (hL1 : ∀ x : NumberField.SUnits.sUnitsRep ℚ F Sℚ, L.hom ((NumberField.SArchIdele.diagS ℚ F Sℚ).hom x) = 0)
  (hL2 : ∀ y : NumberField.SArchIdele.obj ℚ F Sℚ, L.hom y = 0 → ∃ x, (NumberField.SArchIdele.diagS ℚ F Sℚ).hom x = y)

include hL1 in
theorem diagS_toImage : NumberField.SArchIdele.diagS ℚ F Sℚ ≫ RepImage.toImage L = 0 :=
  Rep.hom_ext (DFunLike.ext _ _ fun x => Subtype.ext (hL1 x))

noncomputable def seqEJY : ShortComplex (Rep ℤ (F ≃ₐ[ℚ] F)) :=
  ShortComplex.mk (NumberField.SArchIdele.diagS ℚ F Sℚ) (RepImage.toImage L) (diagS_toImage F Sℚ L hL1)

include hL2 in
theorem seqEJY_shortExact : (seqEJY F Sℚ L hL1).ShortExact where
  exact := (forget₂ (Rep ℤ (F ≃ₐ[ℚ] F)) (ModuleCat ℤ)).reflects_exact_of_faithful _ <|
    (ShortComplex.moduleCat_exact_iff _).2 fun y hy => by
      obtain ⟨x, hx⟩ := hL2 y (congrArg Subtype.val hy)
      exact ⟨x, hx⟩
  mono_f := (Rep.mono_iff_injective _).2 (diagS_injective F Sℚ)
  epi_g := (Rep.epi_iff_surjective _).2 fun y => by
    obtain ⟨x, hx⟩ := y.2
    exact ⟨x, Subtype.ext hx⟩

end seqEJY
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

end Reduce95
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

namespace Reduce95
open ExtCitation

section kappa

variable {p : ℕ} [Fact p.Prime] (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
  (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p)
  {Gd : Type} [Group Gd] (πg : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Gd)
  (B : Rep ℤ Gd) (β : B →+ M.dualTwist (cycloChar p))

theorem p_ne_zero' : p ≠ 0 := (Fact.out : p.Prime).ne_zero

noncomputable def zetaU : (AlgebraicClosure ℚ)ˣ := (hζ.isUnit p_ne_zero').unit

theorem coe_zetaU : ((zetaU ζ hζ : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) = ζ := IsUnit.unit_spec _

theorem zetaU_prim : IsPrimitiveRoot (zetaU ζ hζ) p := hζ.isUnit_unit p_ne_zero'

theorem zetaU_pow_p : zetaU ζ hζ ^ p = 1 := (zetaU_prim ζ hζ).pow_eq_one

noncomputable def expZ : ZMod p →+ Additive (AlgebraicClosure ℚ)ˣ where
  toFun a := Additive.ofMul (zetaU ζ hζ ^ a.val)
  map_zero' := by rw [ZMod.val_zero, pow_zero]; rfl
  map_add' a b := by
    rw [← ofMul_mul, ← pow_add, ZMod.val_add, ← pow_eq_pow_mod _ (zetaU_pow_p ζ hζ)]

theorem toMul_expZ (a : ZMod p) : Additive.toMul (expZ ζ hζ a) = zetaU ζ hζ ^ a.val := rfl

theorem expZ_natCast (n : ℕ) : Additive.toMul (expZ ζ hζ (n : ZMod p)) = zetaU ζ hζ ^ n := by
  rw [toMul_expZ, ZMod.val_natCast, ← pow_eq_pow_mod _ (zetaU_pow_p ζ hζ)]

theorem expZ_injective : Function.Injective (expZ ζ hζ) := by
  intro a b h
  have h' : zetaU ζ hζ ^ a.val = zetaU ζ hζ ^ b.val := congrArg Additive.toMul h
  have := (zetaU_prim ζ hζ).pow_inj (ZMod.val_lt a) (ZMod.val_lt b) h'
  exact ZMod.val_injective p this

theorem exists_expZ_eq_of_pow_eq_one (u : (AlgebraicClosure ℚ)ˣ) (hu : u ^ p = 1) : ∃ a : ZMod p, expZ ζ hζ a = Additive.ofMul u := by
  haveI : NeZero p := ⟨p_ne_zero'⟩
  obtain ⟨i, -, hi⟩ := (zetaU_prim ζ hζ).eq_pow_of_mem_rootsOfUnity ((mem_rootsOfUnity p u).mpr hu)
  exact ⟨(i : ZMod p), congrArg Additive.ofMul ((expZ_natCast ζ hζ i).trans hi)⟩

noncomputable def kappa : B →+ M →+ Additive (AlgebraicClosure ℚ)ˣ where
  toFun b := (expZ ζ hζ).comp ((β b : M.dualTwist (cycloChar p)) : Module.Dual (ZMod p) M).toAddMonoidHom
  map_zero' := by ext m; simp
  map_add' b b' := by ext m; simp

theorem kappa_apply (b : B) (m : M) : kappa M ζ hζ B β b m = expZ ζ hζ (((β b : M.dualTwist (cycloChar p)) : Module.Dual (ZMod p) M) m) := rfl

theorem coe_toMul_kappa (b : B) (m : M) :
    ((Additive.toMul (kappa M ζ hζ B β b m) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) =
      ζ ^ (((β b : M.dualTwist (cycloChar p)) : Module.Dual (ZMod p) M) m).val := by
  rw [kappa_apply, toMul_expZ, Units.val_pow_eq_pow_val, coe_zetaU]

theorem galois_expZ (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (a : ZMod p) :
    (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)).ρ γ (expZ ζ hζ a) = expZ ζ hζ ((cycloChar p γ : ZMod p) * a) := by
  haveI : NeZero p := ⟨p_ne_zero'⟩
  change (Rep.ofMulDistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (AlgebraicClosure ℚ)ˣ).ρ γ (expZ ζ hζ a) = _
  rw [Rep.ofMulDistribMulAction_ρ_apply_apply, toMul_expZ]
  apply congrArg Additive.ofMul
  have hmem : zetaU ζ hζ ∈ rootsOfUnity p (AlgebraicClosure ℚ) := (zetaU_prim ζ hζ).mem_rootsOfUnity
  have hspec := modularCyclotomicCharacter.spec (AlgebraicClosure ℚ) (card_rootsOfUnity_eq_self p) (γ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) hmem

  have h1 : γ • zetaU ζ hζ = zetaU ζ hζ ^ ((cycloChar p γ : ZMod p)).val := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val]
    exact hspec
  rw [smul_pow', h1, ← pow_mul, ZMod.val_mul, ← pow_eq_pow_mod _ (zetaU_pow_p ζ hζ)]

variable (hβeq : ∀ (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (b : B),
    β (B.ρ (πg γ) b) = (M.dualTwist (cycloChar p)).ρ γ (β b))

include hβeq in
theorem kappa_equivariant (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (b : B) (m : M) :
    kappa M ζ hζ B β (B.ρ (πg γ) b) (M.ρ γ m) = (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)).ρ γ (kappa M ζ hζ B β b m) := by
  rw [kappa_apply, kappa_apply, galois_expZ, hβeq]
  congr 1
  change ((cycloChar p γ : ZMod p) • ((((β b : M.dualTwist (cycloChar p)) : Module.Dual (ZMod p) M)) ∘ₗ M.ρ γ⁻¹)) (M.ρ γ m) = _
  rw [LinearMap.smul_apply, LinearMap.comp_apply, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply,
    smul_eq_mul]

variable [FiniteDimensional (ZMod p) M] (hβ : Function.Bijective β) (hB : ∀ b : B, p • b = 0)

include hβ hB in

theorem kappa_perfect (c : B →+ Additive (AlgebraicClosure ℚ)ˣ) : ∃! m : M, ∀ b, kappa M ζ hζ B β b m = c b := by
  haveI : NeZero p := ⟨p_ne_zero'⟩

  have hcp : ∀ b, (Additive.toMul (c b)) ^ p = 1 := by
    intro b
    have : c (p • b) = p • c b := map_nsmul c p b
    rw [hB b, map_zero] at this
    have h2 := congrArg Additive.toMul this
    rw [toMul_zero, toMul_nsmul] at h2
    exact h2.symm

  choose e he using fun b => exists_expZ_eq_of_pow_eq_one ζ hζ (Additive.toMul (c b)) (hcp b)
  have he' : ∀ b, expZ ζ hζ (e b) = c b := fun b => he b
  have eadd : ∀ b b', e (b + b') = e b + e b' := by
    intro b b'
    apply expZ_injective ζ hζ
    rw [map_add, he', he', he', map_add]
  let eh : B →+ ZMod p := { toFun := e, map_zero' := by apply expZ_injective ζ hζ; rw [he', map_zero, map_zero], map_add' := eadd }

  let βe : B ≃+ M.dualTwist (cycloChar p) := AddEquiv.ofBijective β hβ
  let φa : Module.Dual (ZMod p) M →+ ZMod p := eh.comp βe.symm.toAddMonoidHom
  let φ : Module.Dual (ZMod p) (Module.Dual (ZMod p) M) := φa.toZModLinearMap p
  obtain ⟨m, hm⟩ := (Module.evalEquiv (ZMod p) M).surjective φ
  refine ⟨m, fun b => ?_, fun m' hm' => ?_⟩
  · rw [kappa_apply, ← he']
    congr 1
    have h1 : φ ((β b : M.dualTwist (cycloChar p)) : Module.Dual (ZMod p) M) = e b := by
      change eh (βe.symm (βe b)) = e b
      rw [AddEquiv.symm_apply_apply]; rfl
    rw [← h1, ← hm]
    rfl
  ·
    have hall : ∀ f : Module.Dual (ZMod p) M, f m' = f m := by
      intro f
      obtain ⟨b, rfl⟩ := hβ.2 f
      have h1 := hm' b
      rw [kappa_apply, ← he'] at h1
      have h2 := expZ_injective ζ hζ h1
      have h3 : φ ((β b : M.dualTwist (cycloChar p)) : Module.Dual (ZMod p) M) = e b := by
        change eh (βe.symm (βe b)) = e b
        rw [AddEquiv.symm_apply_apply]; rfl
      rw [h2, ← h3, ← hm]
      rfl
    have : (Module.evalEquiv (ZMod p) M) m' = (Module.evalEquiv (ZMod p) M) m := by
      ext f; exact hall f
    exact (Module.evalEquiv (ZMod p) M).injective this

end kappa
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

end Reduce95
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

namespace Reduce95
open ExtCitation GroupCohomology M4aHerbrand
open scoped NumberField.PlaceDecomp NumberField.PlaceTransport

section reppi2
universe u
variable {k G : Type u} [CommRing k] [Group G] {ι : Type u} (Fm : ι → Rep.{u} k G)

theorem incl_hom_apply_self (i : ι) (a : Fm i) : (incl Fm i).hom a i = a := by
  have := congrArg (fun φ => φ.hom a) (incl_proj_self Fm i)
  exact this

theorem incl_hom_apply_of_ne {i j : ι} (h : i ≠ j) (a : Fm i) : (incl Fm i).hom a j = 0 := by
  have := congrArg (fun φ => φ.hom a) (incl_proj_of_ne Fm h)
  exact this

end reppi2
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

section transportD
variable {E K : Type} [Field E] [Field K] [NumberField K] [Algebra E K]

theorem transport_eq_smul {w : HeightOneSpectrum (𝓞 K)} (σ : K ≃ₐ[E] K) (hσ : σ ∈ NumberField.PlaceDecomp.decomp E K w)
    (h : σ • w = w) (z : w.adicCompletion K) :
    NumberField.PlaceTransport.transport σ h z = (⟨σ, hσ⟩ : NumberField.PlaceDecomp.decomp E K w) • z := by
  apply IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext
  rw [NumberField.PlaceTransport.transport_apply, NumberField.PlaceDecomp.smul_def, NumberField.PlaceDecomp.actRingEquiv_apply]

end transportD
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

section iotaCompare

variable (F : Type) [Field F] [NumberField F] [IsGalois ℚ F] (Sℚ : Finset (HeightOneSpectrum (𝓞 ℚ)))
  (Φ : NumberField.SIdele.obj ℚ F Sℚ →+ Additive (AdeleRing (𝓞 F) F)ˣ)
  (hΦS : ∀ (x : NumberField.SIdele.obj ℚ F Sℚ) (v : {v // v ∈ Sℚ}) (w : HeightOneSpectrum (𝓞 F)) (y : F ≃ₐ[ℚ] F)
    (hy : y • w = NumberField.PlaceAbove.above ℚ F v.1),
    NumberField.PlaceTransport.transport y hy (((Additive.toMul (Φ x) : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 w) =
      ((Additive.toMul ((x (Sum.inl (Sum.inl v))).1 y) :
        ((NumberField.PlaceAbove.above ℚ F v.1).adicCompletion F)ˣ) : (NumberField.PlaceAbove.above ℚ F v.1).adicCompletion F))
  (hΦout : ∀ (x : NumberField.SIdele.obj ℚ F Sℚ) (v : {v // v ∉ Sℚ}) (w : HeightOneSpectrum (𝓞 F)) (y : F ≃ₐ[ℚ] F)
    (hy : y • w = NumberField.PlaceAbove.above ℚ F v.1),
    NumberField.PlaceTransport.transport y hy (((Additive.toMul (Φ x) : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 w) =
      (((Additive.toMul ((x (Sum.inl (Sum.inr v))).1 y) :
        ((NumberField.PlaceAbove.above ℚ F v.1).adicCompletionIntegers F)ˣ) :
          (NumberField.PlaceAbove.above ℚ F v.1).adicCompletionIntegers F) : (NumberField.PlaceAbove.above ℚ F v.1).adicCompletion F))
  (hΦinf : ∀ (x : NumberField.SIdele.obj ℚ F Sℚ) (v : InfinitePlace ℚ) (w : InfinitePlace F) (y : F ≃ₐ[ℚ] F)
    (hy : y • w = NumberField.ArchIdele.above ℚ F v),
    NumberField.InfinitePlaceTransport.transport y hy (((Additive.toMul (Φ x) : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w) =
      ((Additive.toMul ((x (Sum.inr v)).1 y) : ((NumberField.ArchIdele.above ℚ F v).Completion)ˣ) :
        (NumberField.ArchIdele.above ℚ F v).Completion))
  (hstab : ∀ w : HeightOneSpectrum (𝓞 F), MulAction.stabilizer (F ≃ₐ[ℚ] F) w = NumberField.PlaceDecomp.decomp ℚ F w)
  (v₀ : {v // v ∈ Sℚ})

open scoped Classical in

noncomputable def fx (x : ((NumberField.PlaceAbove.above ℚ F v₀.1).adicCompletion F)ˣ) : NumberField.SArchIdele.fibre ℚ F Sℚ (Sum.inl v₀) :=
  (Rep.indCoindIso (NumberField.FiniteSIdele.localUnits ℚ F v₀.1)).hom.hom
    (Representation.IndV.mk (NumberField.FiniteSIdele.D ℚ F v₀.1).subtype (NumberField.FiniteSIdele.localUnits ℚ F v₀.1).ρ 1 (Additive.ofMul x))

theorem fx_apply_of_mem (x : ((NumberField.PlaceAbove.above ℚ F v₀.1).adicCompletion F)ˣ) (g : F ≃ₐ[ℚ] F)
    (hg : g ∈ NumberField.FiniteSIdele.D ℚ F v₀.1) :
    (fx F Sℚ v₀ x).1 g = Additive.ofMul ((⟨g, hg⟩ : NumberField.FiniteSIdele.D ℚ F v₀.1) • x) := by
  classical
  rw [fx, indCoindIso_hom_mk_one_apply, indToCoindAux_one_of_mem _ _ _ hg]
  rfl

theorem fx_apply_of_not_mem (x : ((NumberField.PlaceAbove.above ℚ F v₀.1).adicCompletion F)ˣ) (g : F ≃ₐ[ℚ] F)
    (hg : g ∉ NumberField.FiniteSIdele.D ℚ F v₀.1) : (fx F Sℚ v₀ x).1 g = 0 := by
  classical
  rw [fx, indCoindIso_hom_mk_one_apply, indToCoindAux_one_of_not_mem _ _ _ hg]

theorem exists_smul_eq_above (w' : HeightOneSpectrum (𝓞 F)) :
    ∃ y : F ≃ₐ[ℚ] F, y • w' = NumberField.PlaceAbove.above ℚ F (w'.under (𝓞 ℚ)) := by
  have hmem : w' ∈ MulAction.orbit (F ≃ₐ[ℚ] F) (NumberField.PlaceAbove.above ℚ F (w'.under (𝓞 ℚ))) := by
    rw [NumberField.PlaceTransport.orbit_eq_setOf_under_eq]
    exact (NumberField.SUnits.under_above ℚ F _).symm
  obtain ⟨g, hg⟩ := hmem
  exact ⟨g⁻¹, NumberField.PlaceTransport.inv_smul_eq_of_smul_eq hg⟩

noncomputable abbrev xfx (x : ((NumberField.PlaceAbove.above ℚ F v₀.1).adicCompletion F)ˣ) : NumberField.SIdele.obj ℚ F Sℚ :=
  (NumberField.SArchIdele.toSIdele ℚ F Sℚ).hom ((incl (NumberField.SArchIdele.fibre ℚ F Sℚ) (Sum.inl v₀)).hom (fx F Sℚ v₀ x))

theorem xfx_inl_inl_self (x : ((NumberField.PlaceAbove.above ℚ F v₀.1).adicCompletion F)ˣ) : xfx F Sℚ v₀ x (Sum.inl (Sum.inl v₀)) = fx F Sℚ v₀ x := by
  rw [xfx, NumberField.SArchIdele.toSIdele_hom_apply_inl_inl, incl_hom_apply_self]

theorem xfx_inl_inl_of_ne (x : ((NumberField.PlaceAbove.above ℚ F v₀.1).adicCompletion F)ˣ) (v : {v // v ∈ Sℚ}) (hv : v ≠ v₀) :
    xfx F Sℚ v₀ x (Sum.inl (Sum.inl v)) = 0 := by
  rw [xfx, NumberField.SArchIdele.toSIdele_hom_apply_inl_inl]
  exact incl_hom_apply_of_ne _ (fun h => hv (Sum.inl_injective h).symm) _

theorem xfx_inl_inr (x : ((NumberField.PlaceAbove.above ℚ F v₀.1).adicCompletion F)ˣ) (v : {v // v ∉ Sℚ}) :
    xfx F Sℚ v₀ x (Sum.inl (Sum.inr v)) = 0 := by
  rw [xfx, NumberField.SArchIdele.toSIdele_hom_apply_inl_inr]

theorem xfx_inr (x : ((NumberField.PlaceAbove.above ℚ F v₀.1).adicCompletion F)ˣ) (v : InfinitePlace ℚ) :
    xfx F Sℚ v₀ x (Sum.inr v) = 0 := by
  rw [xfx, NumberField.SArchIdele.toSIdele_hom_apply_inr]
  exact incl_hom_apply_of_ne _ Sum.inl_ne_inr _

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

include hΦinf in
theorem Phi_xfx_fst (x : ((NumberField.PlaceAbove.above ℚ F v₀.1).adicCompletion F)ˣ) (w : InfinitePlace F) :
    ((Additive.toMul (Φ (xfx F Sℚ v₀ x)) : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w = 1 := by
  obtain ⟨y, hy⟩ := NumberField.InfinitePlace.exists_smul_eq_of_comap_eq (k := ℚ) (w := w)
    (w' := NumberField.ArchIdele.above ℚ F (w.comap (algebraMap ℚ F))) (NumberField.ArchIdele.comap_above ℚ F _).symm
  have h := hΦinf (xfx F Sℚ v₀ x) (w.comap (algebraMap ℚ F)) w y hy
  rw [xfx_inr] at h
  have h1 : NumberField.InfinitePlaceTransport.transport y hy (((Additive.toMul (Φ (xfx F Sℚ v₀ x)) : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w) = 1 := by
    rw [h]; rfl
  rwa [EmbeddingLike.map_eq_one_iff] at h1

include hΦout in
theorem Phi_xfx_snd_of_not_mem (x : ((NumberField.PlaceAbove.above ℚ F v₀.1).adicCompletion F)ˣ) (w' : HeightOneSpectrum (𝓞 F))
    (hw' : w'.under (𝓞 ℚ) ∉ Sℚ) :
    ((Additive.toMul (Φ (xfx F Sℚ v₀ x)) : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 w' = 1 := by
  obtain ⟨y, hy⟩ := exists_smul_eq_above F w'
  have h := hΦout (xfx F Sℚ v₀ x) ⟨_, hw'⟩ w' y hy
  rw [xfx_inl_inr] at h
  have h1 : NumberField.PlaceTransport.transport y hy (((Additive.toMul (Φ (xfx F Sℚ v₀ x)) : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 w') = 1 := by
    rw [h]; rfl
  rwa [EmbeddingLike.map_eq_one_iff] at h1

include hΦS in
theorem Phi_xfx_snd_of_mem_of_ne (x : ((NumberField.PlaceAbove.above ℚ F v₀.1).adicCompletion F)ˣ) (w' : HeightOneSpectrum (𝓞 F))
    (hw' : w'.under (𝓞 ℚ) ∈ Sℚ) (hne : (⟨_, hw'⟩ : {v // v ∈ Sℚ}) ≠ v₀) :
    ((Additive.toMul (Φ (xfx F Sℚ v₀ x)) : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 w' = 1 := by
  obtain ⟨y, hy⟩ := exists_smul_eq_above F w'
  have h := hΦS (xfx F Sℚ v₀ x) ⟨_, hw'⟩ w' y hy
  rw [xfx_inl_inl_of_ne _ _ _ _ _ hne] at h
  have h1 : NumberField.PlaceTransport.transport y hy (((Additive.toMul (Φ (xfx F Sℚ v₀ x)) : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 w') = 1 := by
    rw [h]; rfl
  rwa [EmbeddingLike.map_eq_one_iff] at h1

include hΦS hstab in

theorem Phi_xfx_snd_above (x : ((NumberField.PlaceAbove.above ℚ F v₀.1).adicCompletion F)ˣ) (w' : HeightOneSpectrum (𝓞 F))
    (y : F ≃ₐ[ℚ] F) (hy : y • w' = NumberField.PlaceAbove.above ℚ F v₀.1) :
    ((Additive.toMul (Φ (xfx F Sℚ v₀ x)) : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 w' =
      finSingle F (NumberField.PlaceAbove.above ℚ F v₀.1) x w' := by
  have h := hΦS (xfx F Sℚ v₀ x) v₀ w' y hy
  rw [xfx_inl_inl_self] at h
  by_cases hyD : y ∈ NumberField.FiniteSIdele.D ℚ F v₀.1
  ·
    have hyw : y • NumberField.PlaceAbove.above ℚ F v₀.1 = NumberField.PlaceAbove.above ℚ F v₀.1 := by
      rw [← MulAction.mem_stabilizer_iff, hstab]; exact hyD
    have hw' : w' = NumberField.PlaceAbove.above ℚ F v₀.1 := by
      rw [← NumberField.PlaceTransport.inv_smul_eq_of_smul_eq hy]
      exact NumberField.PlaceTransport.inv_smul_eq_of_smul_eq hyw
    subst hw'
    rw [fx_apply_of_mem _ _ _ _ _ hyD, toMul_ofMul, NumberField.PlaceDecomp.coe_smul_units, transport_eq_smul y hyD] at h
    rw [finSingle_apply_same]
    exact smul_left_cancel _ h
  ·
    rw [fx_apply_of_not_mem _ _ _ _ _ hyD] at h
    have h1 : NumberField.PlaceTransport.transport y hy (((Additive.toMul (Φ (xfx F Sℚ v₀ x)) : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 w') = 1 := by
      rw [h]; rfl
    rw [EmbeddingLike.map_eq_one_iff] at h1
    have hne : w' ≠ NumberField.PlaceAbove.above ℚ F v₀.1 := by
      intro hw'
      apply hyD
      change y ∈ NumberField.PlaceDecomp.decomp ℚ F _
      rw [← hstab, MulAction.mem_stabilizer_iff]
      rw [hw'] at hy
      exact hy
    rw [h1, finSingle_apply_of_ne _ _ _ hne]

include hΦS hΦout hΦinf hstab in

theorem toMul_Phi_xfx (x : ((NumberField.PlaceAbove.above ℚ F v₀.1).adicCompletion F)ˣ) :
    Additive.toMul (Φ (xfx F Sℚ v₀ x)) = iotaW F (NumberField.PlaceAbove.above ℚ F v₀.1) x := by
  obtain ⟨hι1, hι2, hι3⟩ := iotaW_spec F (NumberField.PlaceAbove.above ℚ F v₀.1) x
  apply idele_ext F
  · rw [hι3]
    apply Units.ext
    funext w
    exact Phi_xfx_fst F Sℚ Φ hΦinf v₀ x w
  · intro w'
    apply Units.ext
    rw [coe_finPart_apply, coe_finPart_apply, coe_iotaW_snd_apply]
    by_cases hvS : w'.under (𝓞 ℚ) ∈ Sℚ
    · by_cases hvv : (⟨_, hvS⟩ : {v // v ∈ Sℚ}) = v₀
      · obtain ⟨y, hy⟩ := exists_smul_eq_above F w'
        have hy' : y • w' = NumberField.PlaceAbove.above ℚ F v₀.1 := by rw [hy, ← hvv]
        exact Phi_xfx_snd_above F Sℚ Φ hΦS hstab v₀ x w' y hy'
      · rw [Phi_xfx_snd_of_mem_of_ne F Sℚ Φ hΦS v₀ x w' hvS hvv, finSingle_apply_of_ne]
        intro hw'
        apply hvv
        apply Subtype.ext
        change w'.under (𝓞 ℚ) = v₀.1
        rw [hw', NumberField.SUnits.under_above]
    · rw [Phi_xfx_snd_of_not_mem F Sℚ Φ hΦout v₀ x w' hvS, finSingle_apply_of_ne]
      intro hw'
      apply hvS
      rw [hw', NumberField.SUnits.under_above]
      exact v₀.2

end iotaCompare
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

end Reduce95
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

namespace Reduce95
open ExtCitation groupCohomology

section levelB

variable {p : ℕ} [Fact p.Prime] (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) [FiniteDimensional (ZMod p) M]
  (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F]

noncomputable abbrev Usub : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) := F.fixingSubgroup.comap (MonoidHom.id _)

noncomputable def Bof : Rep ℤ (↥F ≃ₐ[ℚ] ↥F) :=
  Rep.toIntRep (Rep.res (groupCohomology.levelQuotientEquiv F).symm.toMonoidHom ((M.dualTwist (cycloChar p)).quotientToInvariants (Usub F)))

scoped instance finite_dualTwist : Finite (M.dualTwist (cycloChar p)) := Module.finite_of_finite (ZMod p)

noncomputable scoped instance fintype_Bof : Fintype (Bof M F) :=
  Fintype.ofFinite ↥(Representation.invariants ((M.dualTwist (cycloChar p)).ρ.comp (Usub F).subtype))

noncomputable def betaOf : Bof M F →+ M.dualTwist (cycloChar p) :=
  (Representation.invariants ((M.dualTwist (cycloChar p)).ρ.comp (Usub F).subtype)).subtype.toAddMonoidHom

theorem betaOf_apply (b : Bof M F) : betaOf M F b = ((show ↥(Representation.invariants ((M.dualTwist (cycloChar p)).ρ.comp (Usub F).subtype)) from b) : M.dualTwist (cycloChar p)) := rfl

theorem betaOf_injective : Function.Injective (betaOf M F) := Subtype.val_injective

theorem betaOf_bijective (hFM' : ∀ s ∈ F.fixingSubgroup, ∀ m : M.dualTwist (cycloChar p), (M.dualTwist (cycloChar p)).ρ s m = m) :
    Function.Bijective (betaOf M F) :=
  ⟨Subtype.val_injective, fun m => ⟨(⟨m, fun s => hFM' s.1 s.2 m⟩ : ↥(Representation.invariants ((M.dualTwist (cycloChar p)).ρ.comp (Usub F).subtype))), rfl⟩⟩

theorem betaOf_equivariant (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (b : Bof M F) :
    betaOf M F ((Bof M F).ρ (AlgEquiv.restrictNormalHom ↥F γ) b) = (M.dualTwist (cycloChar p)).ρ γ (betaOf M F b) := by
  have h1 : (groupCohomology.levelQuotientEquiv F).symm (AlgEquiv.restrictNormalHom ↥F γ) = QuotientGroup.mk γ := by
    rw [MulEquiv.symm_apply_eq]; exact (groupCohomology.levelQuotientEquiv_mk F γ).symm
  show (((((M.dualTwist (cycloChar p)).quotientToInvariants (Usub F)).ρ
      ((groupCohomology.levelQuotientEquiv F).symm (AlgEquiv.restrictNormalHom ↥F γ)) b) :
        ↥(Representation.invariants ((M.dualTwist (cycloChar p)).ρ.comp (Usub F).subtype))) : M.dualTwist (cycloChar p)) = _
  rw [h1]
  rfl

theorem Bof_torsion (b : Bof M F) : p • b = 0 := by
  apply betaOf_injective M F
  rw [map_nsmul, map_zero, ← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_self, zero_smul]

theorem relationModuleInt_ι_injective {G : Type} [Group G] (B : Rep ℤ G) : Function.Injective (Rep.relationModuleInt.ι B).hom :=
  fun _ _ h => Subtype.ext h

theorem exact_ι_freeCover {G : Type} [Group G] (B : Rep ℤ G) : Function.Exact (Rep.relationModuleInt.ι B).hom (Rep.freeCover B).hom := by
  intro y
  constructor
  · intro hy; exact ⟨(⟨y, hy⟩ : Rep.relationModule B), rfl⟩
  · rintro ⟨x, rfl⟩; exact x.2

theorem freeCover_surjective {G : Type} [Group G] (B : Rep ℤ G) : Function.Surjective (Rep.freeCover B).hom :=
  (Rep.epi_iff_surjective _).1 (Rep.relationSeqInt_shortExact B).epi_g

scoped instance moduleFinite_free {G : Type} [Group G] [Finite G] (B : Rep ℤ G) [Finite B] : Module.Finite ℤ (Rep.free ℤ G B) :=
  Module.Finite.finsupp

end levelB
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

end Reduce95
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

namespace Reduce95
open ExtCitation GroupCohomology M4aHerbrand
open scoped NumberField.PlaceDecomp NumberField.PlaceTransport

section lamCompare
open scoped Classical

variable (S : Finset Nat.Primes) (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F]
  (D : IdeleGaloisDescent (𝓞 ↥F) ℚ ↥F) (T : Set (HeightOneSpectrum (𝓞 ↥F)))
  [MulDistribMulAction (↥F ≃ₐ[ℚ] ↥F) (AdeleRing (𝓞 ↥F) ↥F)ˣ]
  [MulDistribMulAction (↥F ≃ₐ[ℚ] ↥F) (IdeleClassGroup (𝓞 ↥F) ↥F)]
  [MulDistribMulAction (↥F ≃ₐ[ℚ] ↥F) (SIdeleClassGroup (𝓞 ↥F) ↥F T)]
  (hactI : ∀ (g : ↥F ≃ₐ[ℚ] ↥F) (x : (AdeleRing (𝓞 ↥F) ↥F)ˣ), g • x = D.unitsAct g x)
  (hact : ∀ (g : ↥F ≃ₐ[ℚ] ↥F) (c : IdeleClassGroup (𝓞 ↥F) ↥F), g • c = D.classAct g c)
  (hactS : ∀ (g : ↥F ≃ₐ[ℚ] ↥F) (c : IdeleClassGroup (𝓞 ↥F) ↥F), g • toSIdeleClass (𝓞 ↥F) ↥F T c = toSIdeleClass (𝓞 ↥F) ↥F T (D.classAct g c))
  (Φ : NumberField.SIdele.obj ℚ ↥F (Sq S) →+ Additive (AdeleRing (𝓞 ↥F) ↥F)ˣ)
  (hΦeq : ∀ (g : ↥F ≃ₐ[ℚ] ↥F) (x : NumberField.SIdele.obj ℚ ↥F (Sq S)),
    Φ ((NumberField.SIdele.obj ℚ ↥F (Sq S)).ρ g x) = Additive.ofMul (D.unitsAct g (Additive.toMul (Φ x))))
  (hΦS : ∀ (x : NumberField.SIdele.obj ℚ ↥F (Sq S)) (v : {v // v ∈ Sq S}) (w : HeightOneSpectrum (𝓞 ↥F)) (y : ↥F ≃ₐ[ℚ] ↥F)
    (hy : y • w = NumberField.PlaceAbove.above ℚ ↥F v.1),
    NumberField.PlaceTransport.transport y hy (((Additive.toMul (Φ x) : (AdeleRing (𝓞 ↥F) ↥F)ˣ) : AdeleRing (𝓞 ↥F) ↥F).2 w) =
      ((Additive.toMul ((x (Sum.inl (Sum.inl v))).1 y) :
        ((NumberField.PlaceAbove.above ℚ ↥F v.1).adicCompletion ↥F)ˣ) : (NumberField.PlaceAbove.above ℚ ↥F v.1).adicCompletion ↥F))
  (hΦout : ∀ (x : NumberField.SIdele.obj ℚ ↥F (Sq S)) (v : {v // v ∉ Sq S}) (w : HeightOneSpectrum (𝓞 ↥F)) (y : ↥F ≃ₐ[ℚ] ↥F)
    (hy : y • w = NumberField.PlaceAbove.above ℚ ↥F v.1),
    NumberField.PlaceTransport.transport y hy (((Additive.toMul (Φ x) : (AdeleRing (𝓞 ↥F) ↥F)ˣ) : AdeleRing (𝓞 ↥F) ↥F).2 w) =
      (((Additive.toMul ((x (Sum.inl (Sum.inr v))).1 y) :
        ((NumberField.PlaceAbove.above ℚ ↥F v.1).adicCompletionIntegers ↥F)ˣ) :
          (NumberField.PlaceAbove.above ℚ ↥F v.1).adicCompletionIntegers ↥F) : (NumberField.PlaceAbove.above ℚ ↥F v.1).adicCompletion ↥F))
  (hΦinf : ∀ (x : NumberField.SIdele.obj ℚ ↥F (Sq S)) (v : InfinitePlace ℚ) (w : InfinitePlace ↥F) (y : ↥F ≃ₐ[ℚ] ↥F)
    (hy : y • w = NumberField.ArchIdele.above ℚ ↥F v),
    NumberField.InfinitePlaceTransport.transport y hy (((Additive.toMul (Φ x) : (AdeleRing (𝓞 ↥F) ↥F)ˣ) : AdeleRing (𝓞 ↥F) ↥F).1 w) =
      ((Additive.toMul ((x (Sum.inr v)).1 y) : ((NumberField.ArchIdele.above ℚ ↥F v).Completion)ˣ) :
        (NumberField.ArchIdele.above ℚ ↥F v).Completion))
  (hstab : ∀ w : HeightOneSpectrum (𝓞 ↥F), MulAction.stabilizer (↥F ≃ₐ[ℚ] ↥F) w = NumberField.PlaceDecomp.decomp ℚ ↥F w)
  (ιD : ∀ w : HeightOneSpectrum (𝓞 ↥F),
    Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (w.adicCompletion ↥F)ˣ ⟶
      Rep.res (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype (Rep.ofMulDistribMulAction (↥F ≃ₐ[ℚ] ↥F) (AdeleRing (𝓞 ↥F) ↥F)ˣ))
  (hιD : ∀ (w : HeightOneSpectrum (𝓞 ↥F)) (x : (w.adicCompletion ↥F)ˣ), (ιD w).hom (Additive.ofMul x) = Additive.ofMul (iotaW ↥F w x))

noncomputable abbrev lamW (w : HeightOneSpectrum (𝓞 ↥F)) :
    Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (w.adicCompletion ↥F)ˣ ⟶
      Rep.res (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype (Rep.ofMulDistribMulAction (↥F ≃ₐ[ℚ] ↥F) (IdeleClassGroup (𝓞 ↥F) ↥F)) :=
  ιD w ≫ (Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype).map (qI ↥F D hactI hact)

include hιD in
theorem lamW_hom_apply (w : HeightOneSpectrum (𝓞 ↥F)) (x : (w.adicCompletion ↥F)ˣ) :
    (lamW F D hactI hact ιD w).hom (Additive.ofMul x) = Additive.ofMul (QuotientGroup.mk (iotaW ↥F w x) : IdeleClassGroup (𝓞 ↥F) ↥F) := by
  change (qI ↥F D hactI hact).hom ((ιD w).hom (Additive.ofMul x)) = _
  rw [hιD]
  rfl

theorem lamV_inr_hom_apply {C : Rep ℤ (↥F ≃ₐ[ℚ] ↥F)} (L : NumberField.SArchIdele.obj ℚ ↥F (Sq S) ⟶ C) (q : ↥S)
    (x : ((NumberField.PlaceAbove.above ℚ ↥F (placeOf q.1)).adicCompletion ↥F)ˣ) :
    (lamV S F L (Sum.inr q)).hom (Additive.ofMul x) = L.hom ((incl (NumberField.SArchIdele.fibre ℚ ↥F (Sq S)) (Sum.inl (eS S q))).hom (fx ↥F (Sq S) (eS S q) x)) := by
  rw [lamV, coind_homEquiv_hom_apply]
  rfl

include hΦS hΦout hΦinf hstab hιD in

theorem lamV_inr_eq (q : ↥S) :
    lamV S F (LS ↥F (Sq S) D T hactI hact hactS Φ hΦeq) (Sum.inr q) =
      lamW F D hactI hact ιD (NumberField.PlaceAbove.above ℚ ↥F (placeOf q.1)) ≫
        (Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F (NumberField.PlaceAbove.above ℚ ↥F (placeOf q.1))).subtype).map (qS ↥F D T hact hactS) := by
  apply Rep.hom_ext
  apply DFunLike.ext
  intro a
  obtain ⟨x, rfl⟩ : ∃ x, Additive.ofMul x = a := ⟨Additive.toMul a, rfl⟩
  rw [lamV_inr_hom_apply]
  change (LS ↥F (Sq S) D T hactI hact hactS Φ hΦeq).hom _ = (qS ↥F D T hact hactS).hom ((lamW F D hactI hact ιD _).hom (Additive.ofMul x))
  rw [LS_hom_apply, lamW_hom_apply F D hactI hact ιD hιD]
  have := toMul_Phi_xfx ↥F (Sq S) Φ hΦS hΦout hΦinf hstab (eS S q) x
  rw [xfx] at this
  rw [this]
  rfl

end lamCompare
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

end Reduce95
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

namespace Reduce95
open groupCohomology

section invTransport

variable {G : Type} [Group G] [Fintype G] {C C' : Rep ℤ G} (q : C ⟶ C')
  (hq : ∀ H : Subgroup G, Function.Bijective ((groupCohomology.functor ℤ ↥H 2).map ((Rep.resFunctor H.subtype).map q)).hom)

noncomputable def qH (H : Subgroup G) : groupCohomology (Rep.res H.subtype C) 2 ≃+ groupCohomology (Rep.res H.subtype C') 2 :=
  AddEquiv.ofBijective ((groupCohomology.functor ℤ ↥H 2).map ((Rep.resFunctor H.subtype).map q)).hom.toAddMonoidHom (hq H)

theorem qH_apply (H : Subgroup G) (x : groupCohomology (Rep.res H.subtype C) 2) :
    qH q hq H x = (groupCohomology.map (MonoidHom.id ↥H) ((Rep.resFunctor H.subtype).map q) 2).hom x := rfl

noncomputable abbrev res2 (X : Rep ℤ G) (H : Subgroup G) : groupCohomology X 2 →+ groupCohomology (Rep.res H.subtype X) 2 :=
  (groupCohomology.map H.subtype (𝟙 (Rep.res H.subtype X)) 2).hom.toAddMonoidHom

theorem res2_natural (H : Subgroup G) (x : groupCohomology C 2) :
    res2 C' H ((groupCohomology.map (MonoidHom.id G) q 2).hom x) = qH q hq H (res2 C H x) := by
  have h := (groupCohomology.resNatTrans ℤ H.subtype 2).naturality q
  have h' := congrArg (fun φ => φ.hom x) h
  simp only [groupCohomology.functor_obj, groupCohomology.functor_map, Functor.comp_obj, Functor.comp_map,
    groupCohomology.resNatTrans_app, ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at h'
  exact h'

theorem res2_top_injective (X : Rep ℤ G) : Function.Injective (res2 X (⊤ : Subgroup G)) := by
  obtain ⟨cor, hcor⟩ := groupCohomology.exists_corestriction_comp_res_eq_index_nsmul (⊤ : Subgroup G) X 2
  intro x y h
  have hx := hcor x
  have hy := hcor y
  rw [Subgroup.index_top, one_smul] at hx hy
  rw [← hx, ← hy]
  exact congrArg cor h

variable (invG : groupCohomology C 2 →+ AddCircle (1 : ℚ))
  (inv : ∀ H : Subgroup G, groupCohomology (Rep.res H.subtype C) 2 →+ AddCircle (1 : ℚ))
  (hinjG : Function.Injective invG) (hinj : ∀ H, Function.Injective (inv H))
  (hrangeG : ∀ t : AddCircle (1 : ℚ), t ∈ invG.range ↔ Nat.card G • t = 0)
  (hrange : ∀ (H : Subgroup G) (t : AddCircle (1 : ℚ)), t ∈ (inv H).range ↔ Nat.card ↥H • t = 0)
  (hii : ∀ (H : Subgroup G) (x : groupCohomology C 2), inv H (res2 C H x) = H.index • invG x)

include hinj hrangeG hrange hii in

theorem res2_top_surjective : Function.Surjective (res2 C (⊤ : Subgroup G)) := by
  intro z
  have hz : inv ⊤ z ∈ (inv ⊤).range := ⟨z, rfl⟩
  rw [hrange, Subgroup.card_top, ← hrangeG] at hz
  obtain ⟨x, hx⟩ := hz
  refine ⟨x, hinj ⊤ ?_⟩
  rw [hii, Subgroup.index_top, one_smul, hx]

include hq hinj hrangeG hrange hii in

theorem qG_bijective : Function.Bijective (groupCohomology.map (MonoidHom.id G) q 2).hom := by
  constructor
  · intro x y h
    have h1 := congrArg (res2 C' ⊤) h
    rw [res2_natural q hq, res2_natural q hq] at h1
    exact res2_top_injective C ((qH q hq ⊤).injective h1)
  · intro c
    obtain ⟨z, hz⟩ := (qH q hq ⊤).surjective (res2 C' ⊤ c)
    obtain ⟨x, hx⟩ := res2_top_surjective invG inv hinj hrangeG hrange hii z
    refine ⟨x, res2_top_injective C' ?_⟩
    rw [res2_natural q hq, hx, hz]

noncomputable def qG : groupCohomology C 2 ≃+ groupCohomology C' 2 :=
  AddEquiv.ofBijective (groupCohomology.map (MonoidHom.id G) q 2).hom.toAddMonoidHom (qG_bijective q hq invG inv hinj hrangeG hrange hii)

theorem qG_apply (x : groupCohomology C 2) :
    qG q hq invG inv hinj hrangeG hrange hii x = (groupCohomology.map (MonoidHom.id G) q 2).hom x := rfl

noncomputable def invG' : groupCohomology C' 2 →+ AddCircle (1 : ℚ) :=
  invG.comp (qG q hq invG inv hinj hrangeG hrange hii).symm.toAddMonoidHom

noncomputable def inv' (H : Subgroup G) : groupCohomology (Rep.res H.subtype C') 2 →+ AddCircle (1 : ℚ) :=
  (inv H).comp (qH q hq H).symm.toAddMonoidHom

theorem invG'_apply (x : groupCohomology C 2) :
    invG' q hq invG inv hinj hrangeG hrange hii ((groupCohomology.map (MonoidHom.id G) q 2).hom x) = invG x := by
  change invG ((qG q hq invG inv hinj hrangeG hrange hii).symm (qG q hq invG inv hinj hrangeG hrange hii x)) = invG x
  rw [AddEquiv.symm_apply_apply]

theorem inv'_apply (H : Subgroup G) (x : groupCohomology (Rep.res H.subtype C) 2) :
    inv' q hq inv H ((groupCohomology.map (MonoidHom.id ↥H) ((Rep.resFunctor H.subtype).map q) 2).hom x) = inv H x := by
  change inv H ((qH q hq H).symm (qH q hq H x)) = inv H x
  rw [AddEquiv.symm_apply_apply]

include hinjG in
theorem invG'_injective : Function.Injective (invG' q hq invG inv hinj hrangeG hrange hii) :=
  hinjG.comp (qG q hq invG inv hinj hrangeG hrange hii).symm.injective

include hinj in
theorem inv'_injective (H : Subgroup G) : Function.Injective (inv' q hq inv H) := (hinj H).comp (qH q hq H).symm.injective

include hrangeG in
theorem invG'_range (t : AddCircle (1 : ℚ)) : t ∈ (invG' q hq invG inv hinj hrangeG hrange hii).range ↔ Nat.card G • t = 0 := by
  rw [← hrangeG]
  constructor
  · rintro ⟨x, rfl⟩; exact ⟨_, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨qG q hq invG inv hinj hrangeG hrange hii x, by
      change invG ((qG q hq invG inv hinj hrangeG hrange hii).symm (qG q hq invG inv hinj hrangeG hrange hii x)) = invG x
      rw [AddEquiv.symm_apply_apply]⟩

variable (hv : ∀ (H : Subgroup G) (cor : groupCohomology (Rep.res H.subtype C) 2 →+ groupCohomology C 2),
    (∀ x : groupCohomology C 2, cor (res2 C H x) = H.index • x) → ∀ y, invG (cor y) = inv H y)

include hv in

theorem invG'_cor (H : Subgroup G) (cor' : groupCohomology (Rep.res H.subtype C') 2 →+ groupCohomology C' 2)
    (hcor' : ∀ x : groupCohomology C' 2, cor' (res2 C' H x) = H.index • x) (y : groupCohomology (Rep.res H.subtype C') 2) :
    invG' q hq invG inv hinj hrangeG hrange hii (cor' y) = inv' q hq inv H y := by
  let eG := qG q hq invG inv hinj hrangeG hrange hii
  let cor : groupCohomology (Rep.res H.subtype C) 2 →+ groupCohomology C 2 :=
    eG.symm.toAddMonoidHom.comp (cor'.comp (qH q hq H).toAddMonoidHom)
  have hcor : ∀ x : groupCohomology C 2, cor (res2 C H x) = H.index • x := by
    intro x
    change eG.symm (cor' (qH q hq H (res2 C H x))) = H.index • x
    rw [← res2_natural q hq, ← qG_apply q hq invG inv hinj hrangeG hrange hii, hcor', ← map_nsmul, AddEquiv.symm_apply_apply]
  have h := hv H cor hcor ((qH q hq H).symm y)
  change invG (eG.symm (cor' (qH q hq H ((qH q hq H).symm y)))) = inv H ((qH q hq H).symm y) at h
  rw [AddEquiv.apply_symm_apply] at h
  exact h

end invTransport
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

end Reduce95
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

namespace Reduce95
open groupCohomology

section alpha

variable (p : ℕ) [Fact p.Prime]

theorem coe_natCast_eq_zero (k : ℕ) : (((k : ℚ)) : AddCircle (1 : ℚ)) = 0 := by
  rw [AddCircle.coe_eq_zero_iff]
  exact ⟨k, by simp⟩

noncomputable def ep : ZMod p →+ AddCircle (1 : ℚ) where
  toFun a := (((a.val : ℚ) / (p : ℚ) : ℚ) : AddCircle (1 : ℚ))
  map_zero' := by rw [ZMod.val_zero, Nat.cast_zero, zero_div]; rfl
  map_add' a b := by
    have hp : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
    have h := Nat.mod_add_div (a.val + b.val) p
    rw [ZMod.val_add]
    have h2 : ((a.val : ℚ) / p + (b.val : ℚ) / p) = ((((a.val + b.val) % p : ℕ) : ℚ) / p) + (((a.val + b.val) / p : ℕ) : ℚ) := by
      have h3 : (((a.val + b.val) % p : ℕ) : ℚ) + (p : ℚ) * (((a.val + b.val) / p : ℕ) : ℚ) = (a.val : ℚ) + b.val := by
        exact_mod_cast h
      field_simp
      linarith
    rw [← QuotientAddGroup.mk_add, h2, QuotientAddGroup.mk_add, coe_natCast_eq_zero, add_zero]

theorem ep_apply (a : ZMod p) : ep p a = (((a.val : ℚ) / (p : ℚ) : ℚ) : AddCircle (1 : ℚ)) := rfl

theorem ep_injective : Function.Injective (ep p) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  rw [injective_iff_map_eq_zero]
  intro a ha
  rw [ep_apply, AddCircle.coe_eq_zero_iff] at ha
  obtain ⟨n, hn⟩ := ha
  rw [zsmul_one] at hn
  have hp : (0 : ℚ) < p := Nat.cast_pos.2 (Fact.out : p.Prime).pos
  have h1 : (n : ℚ) * p = a.val := by field_simp at hn; linarith [hn]
  have h2 : (n : ℚ) * p < p := by rw [h1]; exact_mod_cast ZMod.val_lt a
  have h3 : 0 ≤ (n : ℚ) * p := by rw [h1]; exact_mod_cast Nat.zero_le _
  have hn0 : n = 0 := by
    have : (n : ℚ) < 1 := by nlinarith
    have : (0 : ℚ) ≤ n := by nlinarith
    have h4 : n < 1 := by exact_mod_cast ‹(n : ℚ) < 1›
    have h5 : 0 ≤ n := by exact_mod_cast ‹(0 : ℚ) ≤ n›
    omega
  rw [hn0, Int.cast_zero, zero_mul] at h1
  have : a.val = 0 := by exact_mod_cast h1.symm
  rw [← ZMod.natCast_zmod_val a, this, Nat.cast_zero]

theorem nsmul_ep_eq_zero_of_dvd {m : ℕ} (hm : p ∣ m) (a : ZMod p) : m • ep p a = 0 := by
  rw [← map_nsmul, nsmul_eq_mul, (ZMod.natCast_eq_zero_iff m p).2 hm, zero_mul, map_zero]

variable {G : Type} [Group G] [Fintype G] (C : Rep ℤ G)
  (invG : groupCohomology C 2 →+ AddCircle (1 : ℚ)) (hinv : Function.Injective invG)
  (hrangeG : ∀ t : AddCircle (1 : ℚ), t ∈ invG.range ↔ Nat.card G • t = 0)
  (hpG : p ∣ Nat.card G)
  (B : Rep ℤ G) [Fintype B] (hX : (Rep.relationSeqInt B).ShortExact)
  (al : (Rep.relationModuleInt B ⟶ C) →+ (groupCohomology B 1 →+ ZMod p))
  (hal : ∀ (φ : Rep.relationModuleInt B ⟶ C) (y : groupCohomology B 1),
    invG ((groupCohomology.map (MonoidHom.id G) φ 2).hom ((groupCohomology.δ hX 1 2 rfl).hom y)) = ((((al φ y).val : ℚ) / (p : ℚ) : ℚ) : AddCircle (1 : ℚ)))
  (hSURJ : ∀ θ : groupCohomology B 1 →+ groupCohomology C 2, ∃ φ : Rep.relationModuleInt B ⟶ C, ∀ y : groupCohomology B 1,
    (groupCohomology.map (MonoidHom.id G) φ 2).hom ((groupCohomology.δ hX 1 2 rfl).hom y) = θ y)

include hinv hrangeG hpG hal hSURJ in

theorem al_surjective (g : groupCohomology B 1 →+ ZMod p) : ∃ φ : Rep.relationModuleInt B ⟶ C, al φ = g := by

  have hmem : ∀ y, ep p (g y) ∈ invG.range := by
    intro y
    rw [hrangeG]
    exact nsmul_ep_eq_zero_of_dvd p hpG (g y)
  choose c hc using hmem
  have cadd : ∀ y y', c (y + y') = c y + c y' := by
    intro y y'
    apply hinv
    rw [map_add, hc, hc, hc, map_add, map_add]
  let θ : groupCohomology B 1 →+ groupCohomology C 2 :=
    { toFun := c, map_zero' := by apply hinv; rw [hc, map_zero, map_zero, map_zero], map_add' := cadd }
  obtain ⟨φ, hφ⟩ := hSURJ θ
  refine ⟨φ, ?_⟩
  ext y
  apply ep_injective p
  rw [ep_apply, ← hal, hφ]
  exact hc y

end alpha
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

end Reduce95
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

namespace Reduce95
open ExtCitation groupCohomology GroupCohomology M4aHerbrand
open scoped NumberField.PlaceDecomp NumberField.PlaceTransport

theorem restrictNormalHom_eq_one_of_mem (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [Normal ℚ ↥F]
    (s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hs : s ∈ F.fixingSubgroup) : AlgEquiv.restrictNormalHom ↥F s = 1 := by
  apply AlgEquiv.ext
  intro a
  apply (algebraMap ↥F (AlgebraicClosure ℚ)).injective
  change (algebraMap ↥F (AlgebraicClosure ℚ)) (s.restrictNormal ↥F a) = algebraMap ↥F (AlgebraicClosure ℚ) a
  rw [AlgEquiv.restrictNormal_commutes]
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hs a a.2

section leveldefs

variable (S : Finset Nat.Primes) (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F]

noncomputable def DD : IdeleGaloisDescent (𝓞 ↥F) ℚ ↥F := Classical.choice (M4aHerbrand.nonempty_ideleGaloisDescent ℚ ↥F)

abbrev TT : Set (HeightOneSpectrum (𝓞 ↥F)) := NumberField.placesOverPrimes ↥F (↑S : Set Nat.Primes)

theorem DD_stab : (DD F).StabilizesUnitIdeles (TT S F) :=
  M4aHerbrand.IdeleGaloisDescent.stabilizesUnitIdeles_placesOverPrimes ℚ ↥F (DD F) ↑S

noncomputable scoped instance instActI : MulDistribMulAction (↥F ≃ₐ[ℚ] ↥F) (AdeleRing (𝓞 ↥F) ↥F)ˣ := idelesAction ℚ ↥F (DD F)
noncomputable scoped instance instActC : MulDistribMulAction (↥F ≃ₐ[ℚ] ↥F) (IdeleClassGroup (𝓞 ↥F) ↥F) := (DD F).classMulDistribMulAction
noncomputable scoped instance instActCS : MulDistribMulAction (↥F ≃ₐ[ℚ] ↥F) (SIdeleClassGroup (𝓞 ↥F) ↥F (TT S F)) :=
  (DD F).sClassMulDistribMulAction (DD_stab S F)

theorem hactI_F : ∀ (g : ↥F ≃ₐ[ℚ] ↥F) (x : (AdeleRing (𝓞 ↥F) ↥F)ˣ), g • x = (DD F).unitsAct g x := fun _ _ => rfl
theorem hact_F : ∀ (g : ↥F ≃ₐ[ℚ] ↥F) (c : IdeleClassGroup (𝓞 ↥F) ↥F), g • c = (DD F).classAct g c := fun _ _ => rfl
theorem hactS_F : ∀ (g : ↥F ≃ₐ[ℚ] ↥F) (c : IdeleClassGroup (𝓞 ↥F) ↥F),
    g • toSIdeleClass (𝓞 ↥F) ↥F (TT S F) c = toSIdeleClass (𝓞 ↥F) ↥F (TT S F) ((DD F).classAct g c) :=
  fun g c => (DD F).sClassMulDistribMulAction_smul_toSIdeleClass (DD_stab S F) g c

noncomputable def PhiF : NumberField.SIdele.obj ℚ ↥F (Sq S) →+ Additive (AdeleRing (𝓞 ↥F) ↥F)ˣ :=
  (NumberField.SIdele.exists_addMonoidHom_obj_adeleRing_units_apply ℚ ↥F (Sq S) (DD F)).choose

def PhiF_spec := (NumberField.SIdele.exists_addMonoidHom_obj_adeleRing_units_apply ℚ ↥F (Sq S) (DD F)).choose_spec

theorem PhiF_inj : Function.Injective (PhiF S F) := (PhiF_spec S F).1
def PhiF_range := (PhiF_spec S F).2.1
def PhiF_eq := (PhiF_spec S F).2.2.1
def PhiF_diag := (PhiF_spec S F).2.2.2.1
def PhiF_S := (PhiF_spec S F).2.2.2.2.1
def PhiF_out := (PhiF_spec S F).2.2.2.2.2.1
def PhiF_inf := (PhiF_spec S F).2.2.2.2.2.2

noncomputable def LF : NumberField.SArchIdele.obj ℚ ↥F (Sq S) ⟶ Rep.ofMulDistribMulAction (↥F ≃ₐ[ℚ] ↥F) (SIdeleClassGroup (𝓞 ↥F) ↥F (TT S F)) :=
  LS ↥F (Sq S) (DD F) (TT S F) (hactI_F F) (hact_F F) (hactS_F S F) (PhiF S F) (PhiF_eq S F)

def J_c_F := NumberField.SArchIdele.toSIdeleClass_mk_comp_diagS_eq_one_and_exists_of_eq_one ℚ ↥F (Sq S) (PhiF S F)
  (PhiF_inj S F) (PhiF_range S F) (PhiF_S S F) (PhiF_out S F) (PhiF_inf S F) (PhiF_diag S F)

theorem hL1F (x : NumberField.SUnits.sUnitsRep ℚ ↥F (Sq S)) : (LF S F).hom ((NumberField.SArchIdele.diagS ℚ ↥F (Sq S)).hom x) = 0 := by
  have h := (J_c_F S F).1 x
  rw [setOf_under_mem_Sq S ↥F] at h
  unfold LF
  rw [LS_hom_apply, h]
  rfl

theorem hL2F (y : NumberField.SArchIdele.obj ℚ ↥F (Sq S)) (hy : (LF S F).hom y = 0) :
    ∃ x, (NumberField.SArchIdele.diagS ℚ ↥F (Sq S)).hom x = y := by
  have h := (J_c_F S F).2 y
  rw [setOf_under_mem_Sq S ↥F] at h
  apply h
  unfold LF at hy
  rw [LS_hom_apply] at hy
  exact Additive.ofMul.injective hy

noncomputable abbrev seqF : ShortComplex (Rep ℤ (↥F ≃ₐ[ℚ] ↥F)) := seqEJY ↥F (Sq S) (LF S F) (hL1F S F)

theorem seqF_shortExact : (seqF S F).ShortExact := seqEJY_shortExact ↥F (Sq S) (LF S F) (hL1F S F) (hL2F S F)

end leveldefs
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

section leveldefsM

variable {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
  (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) [FiniteDimensional (ZMod p) M]
  (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p)
  (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F]
  (hFS : F.IsUnramifiedOutside S)
  (hFM' : ∀ s ∈ F.fixingSubgroup, ∀ m : M.dualTwist (cycloChar p), (M.dualTwist (cycloChar p)).ρ s m = m)

noncomputable abbrev RB : Rep ℤ (↥F ≃ₐ[ℚ] ↥F) := Rep.relationModuleInt (Bof M F)

scoped instance : Module.Free ℤ (Rep.relationCarrier (Bof M F)) := by
  haveI : Fintype (↥F ≃ₐ[ℚ] ↥F) := Fintype.ofFinite _
  exact Rep.moduleFree_relationCarrier (Bof M F)

theorem hT_F : ((seqF S F).map (ihom (RB M F))).ShortExact :=
  Rep.shortExact_map_ihom_of_free (Rep.relationCarrier (Bof M F)) (Rep.relationRepInt (Bof M F)) (seqF_shortExact S F)

noncomputable def dYF : (RB M F ⟶ (seqF S F).X₃) →+ H1 ((ihom (RB M F)).obj (seqF S F).X₁) :=
  ((groupCohomology.δ (hT_F S M F) 0 1 rfl).hom.toAddMonoidHom.comp
    (groupCohomology.H0Iso ((ihom (RB M F)).obj (seqF S F).X₃)).inv.hom.toAddMonoidHom).comp
    (Representation.linHom.invariantsEquivRepHom (RB M F) (seqF S F).X₃).symm.toLinearMap.toAddMonoidHom

theorem dYF_apply (t : RB M F ⟶ (seqF S F).X₃) : dYF S M F t = (groupCohomology.δ (hT_F S M F) 0 1 rfl).hom
    ((groupCohomology.H0Iso ((ihom (RB M F)).obj (seqF S F).X₃)).inv ((Representation.linHom.invariantsEquivRepHom (RB M F) (seqF S F).X₃).symm t)) := rfl

theorem hLESa_F (x : H1 ((ihom (RB M F)).obj (seqF S F).X₁))
    (hx : (groupCohomology.map (MonoidHom.id _) ((ihom (RB M F)).map (seqF S F).f) 1).hom x = 0) : ∃ t, dYF S M F t = x :=
  Rep.exists_delta_hom_eq_of_map_ihom_map_eq_zero (RB M F) (hT_F S M F) x hx

theorem hLESb_F (t : RB M F ⟶ (seqF S F).X₃) (ht : dYF S M F t = 0) : ∃ s : RB M F ⟶ (seqF S F).X₂, t = s ≫ (seqF S F).g :=
  Rep.exists_eq_comp_of_delta_hom_eq_zero (RB M F) (hT_F S M F) t ht

theorem hLESc_F (s : RB M F ⟶ (seqF S F).X₂) : dYF S M F (s ≫ (seqF S F).g) = 0 :=
  Rep.delta_hom_comp_eq_zero (RB M F) (hT_F S M F) s

include hFS in
theorem hπlev_F : ∃ F' : IntermediateField ℚ (AlgebraicClosure ℚ), F'.IsUnramifiedOutside S ∧
    ∀ s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, s ∈ F'.fixingSubgroup → AlgEquiv.restrictNormalHom ↥F s = 1 :=
  ⟨F, hFS, fun s hs => restrictNormalHom_eq_one_of_mem F s hs⟩

def hdiv_F := NumberField.SUnits.exists_ihom_extension_fixed_of_sLevel_of_injective S hpS (Sq S) (coe_Sq S) F hFS
    (Rep.relationModuleInt.ι (Bof M F)) (Rep.freeCover (Bof M F)) (relationModuleInt_ι_injective (Bof M F)) (exact_ι_freeCover (Bof M F))
    (freeCover_surjective (Bof M F)) (Bof_torsion M F) (iotaE F (Sq S)) (toMul_iotaE F (Sq S))

include hpS hFS hFM' in

theorem exists_LE2_F : ∃ Λ : H1 ((ihom (RB M F)).obj (NumberField.SUnits.sUnitsRep ℚ ↥F (Sq S))) →+ continuousH2S S M,
    IsGlobalBridge₂ S (AlgEquiv.restrictNormalHom ↥F) (Rep.relationModuleInt.ι (Bof M F)) (Rep.freeCover (Bof M F))
      (A := Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)) (iotaE F (Sq S)) (kappa M ζ hζ (Bof M F) (betaOf M F)) Λ := by
  have hκeq := kappa_equivariant M ζ hζ (AlgEquiv.restrictNormalHom ↥F) (Bof M F) (betaOf M F) (betaOf_equivariant M F)
  have hκ := kappa_perfect M ζ hζ (Bof M F) (betaOf M F) (betaOf_bijective M F hFM') (Bof_torsion M F)
  have hdiv := hdiv_F S hpS M F hFS
  exact groupCohomology.exists_isGlobalBridge2 S (AlgEquiv.restrictNormalHom ↥F) (hπlev_F S F hFS)
    (Rep.relationModuleInt.ι (Bof M F)) (Rep.freeCover (Bof M F)) (exact_ι_freeCover (Bof M F)) (freeCover_surjective (Bof M F))
    (X := NumberField.SUnits.sUnitsRep ℚ ↥F (Sq S)) (A := Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ))
    (iotaE F (Sq S)) (iotaE_injective F (Sq S)) (iotaE_equivariant F (Sq S))
    (p := p) (M := M) (kappa M ζ hζ (Bof M F) (betaOf M F)) hκeq hκ hdiv

noncomputable def LE2F : H1 ((ihom (RB M F)).obj (NumberField.SUnits.sUnitsRep ℚ ↥F (Sq S))) →+ continuousH2S S M :=
  (exists_LE2_F S hpS M ζ hζ F hFS hFM').choose

include hpS hFS hFM' in
theorem LE2F_spec : IsGlobalBridge₂ S (AlgEquiv.restrictNormalHom ↥F) (Rep.relationModuleInt.ι (Bof M F)) (Rep.freeCover (Bof M F))
      (A := Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)) (iotaE F (Sq S)) (kappa M ζ hζ (Bof M F) (betaOf M F)) (LE2F S hpS M ζ hζ F hFS hFM') :=
  (exists_LE2_F S hpS M ζ hζ F hFS hFM').choose_spec

end leveldefsM
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

end Reduce95
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

namespace Reduce95
open ExtCitation groupCohomology GroupCohomology M4aHerbrand
open scoped NumberField.PlaceDecomp NumberField.PlaceTransport

section levelInv

variable (S : Finset Nat.Primes) (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F]

theorem exists_iotaD_F : ∃ ιD : ∀ w : HeightOneSpectrum (𝓞 ↥F),
    Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (w.adicCompletion ↥F)ˣ ⟶
      Rep.res (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype (Rep.ofMulDistribMulAction (↥F ≃ₐ[ℚ] ↥F) (AdeleRing (𝓞 ↥F) ↥F)ˣ),
    ∀ (w : HeightOneSpectrum (𝓞 ↥F)) (x : (w.adicCompletion ↥F)ˣ), (ιD w).hom (Additive.ofMul x) = Additive.ofMul (iotaW ↥F w x) :=
  M4aHerbrand.exists_hom_adicCompletion_res_decomp_ideles_apply ℚ ↥F (DD F) (hactI_F F) (iotaW ↥F) (iotaW_spec ↥F)

noncomputable def iotaDF := (exists_iotaD_F F).choose

theorem iotaDF_spec (w : HeightOneSpectrum (𝓞 ↥F)) (x : (w.adicCompletion ↥F)ˣ) :
    (iotaDF F w).hom (Additive.ofMul x) = Additive.ofMul (iotaW ↥F w x) := (exists_iotaD_F F).choose_spec w x

noncomputable abbrev lamWF (w : HeightOneSpectrum (𝓞 ↥F)) := lamW F (DD F) (hactI_F F) (hact_F F) (iotaDF F) w

theorem lamWF_apply (w : HeightOneSpectrum (𝓞 ↥F)) (x : (w.adicCompletion ↥F)ˣ) :
    (lamWF F w).hom (Additive.ofMul x) = Additive.ofMul (QuotientGroup.mk (iotaW ↥F w x) : IdeleClassGroup (𝓞 ↥F) ↥F) :=
  lamW_hom_apply F (DD F) (hactI_F F) (hact_F F) (iotaDF F) (iotaDF_spec F) w x

noncomputable abbrev qSF := qS ↥F (DD F) (TT S F) (hact_F F) (hactS_F S F)

variable (hunr : ∀ w : HeightOneSpectrum (𝓞 ↥F), w ∉ TT S F → Ideal.ramificationIdx' (w.asIdeal.under (𝓞 ℚ)) w.asIdeal = 1)

include hunr in
theorem qSF_bijective (H : Subgroup (↥F ≃ₐ[ℚ] ↥F)) :
    Function.Bijective ((groupCohomology.functor ℤ ↥H 2).map ((Rep.resFunctor H.subtype).map (qSF S F))).hom :=
  M4aHerbrand.bijective_groupCohomology_map_toSIdeleClass ℚ ↥F (DD F) (TT S F) hunr (DD_stab S F) (hact_F F) (hactS_F S F) H 1

end levelInv
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

end Reduce95
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

namespace Reduce95
open ExtCitation
open scoped NumberField.PlaceDecomp

section coords

variable (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F] (q : Nat.Primes)

local instance factPrimes (q : Nat.Primes) : Fact ((q : ℕ)).Prime := ⟨q.2⟩

noncomputable abbrev wq : HeightOneSpectrum (𝓞 ↥F) := NumberField.PlaceAbove.above ℚ ↥F (placeOf q)

theorem natCast_mem_wq : ((q : ℕ) : 𝓞 ↥F) ∈ (wq F q).asIdeal := by
  have h1 : ((q : ℕ) : 𝓞 ℚ) ∈ ((wq F q).under (𝓞 ℚ)).asIdeal := by
    rw [NumberField.SUnits.under_above]; exact natCast_mem_asIdeal_placeOf q
  have : algebraMap (𝓞 ℚ) (𝓞 ↥F) (((q : ℕ) : 𝓞 ℚ)) ∈ (wq F q).asIdeal := h1
  rwa [map_natCast] at this

def coordsQ := NumberField.PlaceDecomp.exists_ringHom_adicCompletion_padicAlgCl_extends_padicEmbedding (q : ℕ) F (wq F q) (natCast_mem_wq F q)

noncomputable def sigmaQ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ := (coordsQ F q).choose

noncomputable def PhiQ : (wq F q).adicCompletion ↥F →+* PadicAlgCl q := (coordsQ F q).choose_spec.choose

def PhiQ_spec := (coordsQ F q).choose_spec.choose_spec

theorem hPhiF_q : ∀ x : ↥F, PhiQ F q (algebraMap ↥F ((wq F q).adicCompletion ↥F) x) = padicEmbedding q (sigmaQ F q (x : AlgebraicClosure ℚ)) :=
  (PhiQ_spec F q).1

theorem hcont_q : Continuous (PhiQ F q) := (PhiQ_spec F q).2.2.2.2

noncomputable def piQ : primeLocalGaloisGroup q →* ↥(NumberField.PlaceDecomp.decomp ℚ ↥F (wq F q)) where
  toFun τ := ⟨AlgEquiv.restrictNormalHom ↥F ((sigmaQ F q)⁻¹ * primeLocalToGlobal q τ * sigmaQ F q), (PhiQ_spec F q).2.1 τ⟩
  map_one' := Subtype.ext (by simp)
  map_mul' τ τ' := Subtype.ext (by
    change AlgEquiv.restrictNormalHom ↥F ((sigmaQ F q)⁻¹ * primeLocalToGlobal q (τ * τ') * sigmaQ F q) =
      AlgEquiv.restrictNormalHom ↥F ((sigmaQ F q)⁻¹ * primeLocalToGlobal q τ * sigmaQ F q) *
        AlgEquiv.restrictNormalHom ↥F ((sigmaQ F q)⁻¹ * primeLocalToGlobal q τ' * sigmaQ F q)
    rw [← map_mul (AlgEquiv.restrictNormalHom ↥F), map_mul (primeLocalToGlobal q)]
    congr 1
    group)

theorem hpi_q : ∀ τ : primeLocalGaloisGroup q, ((piQ F q τ : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F (wq F q))) : ↥F ≃ₐ[ℚ] ↥F) =
    AlgEquiv.restrictNormalHom ↥F ((sigmaQ F q)⁻¹ * primeLocalToGlobal q τ * sigmaQ F q) := fun _ => rfl

theorem hpisurj_q : Function.Surjective (piQ F q) := by
  intro d
  obtain ⟨τ, hτ⟩ := (PhiQ_spec F q).2.2.1 d
  exact ⟨τ, Subtype.ext hτ.symm⟩

theorem heqv_q : ∀ (τ : primeLocalGaloisGroup q) (x : (wq F q).adicCompletion ↥F),
    PhiQ F q (piQ F q τ • x) = (show PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q from τ) (PhiQ F q x) :=
  fun τ x => (PhiQ_spec F q).2.2.2.1 (piQ F q τ) τ rfl x

end coords
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

end Reduce95
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

namespace Reduce95
open ExtCitation

section kappaT

variable {p : ℕ} [Fact p.Prime] (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
  {Gd : Type} [Group Gd] (B : Rep ℤ Gd) {A₀ : Type} [AddCommGroup A₀] (κ : B →+ M →+ A₀)
  {A : Type} [AddCommGroup A] (e : A₀ →+ A) (θ : M ≃ₗ[ZMod p] M)

noncomputable def rhoEquiv (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) : M ≃ₗ[ZMod p] M :=
  { M.ρ g with
    invFun := M.ρ g⁻¹
    left_inv := fun m => by
      change (M.ρ g⁻¹ * M.ρ g) m = m
      rw [← map_mul, inv_mul_cancel, map_one]; rfl
    right_inv := fun m => by
      change (M.ρ g * M.ρ g⁻¹) m = m
      rw [← map_mul, mul_inv_cancel, map_one]; rfl }

@[scoped simp] theorem rhoEquiv_apply (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (m : M) : rhoEquiv M g m = M.ρ g m := rfl

noncomputable def kappaT : B →+ M →+ A where
  toFun b := e.comp ((κ b).comp θ.toLinearMap.toAddMonoidHom)
  map_zero' := by ext m; simp
  map_add' b b' := by ext m; simp

theorem kappaT_apply (b : B) (m : M) : kappaT M B κ e θ b m = e (κ b (θ m)) := rfl

variable (he : Function.Injective e) (hrange : ∀ a : A, p • a = 0 → ∃ x, e x = a) (hB : ∀ b : B, p • b = 0)
  (hκ : ∀ c : B →+ A₀, ∃! m : M, ∀ b, κ b m = c b)

include he hrange hB hκ in

theorem kappaT_perfect (c : B →+ A) : ∃! m : M, ∀ b, kappaT M B κ e θ b m = c b := by
  have hcp : ∀ b, p • c b = 0 := fun b => by rw [← map_nsmul, hB, map_zero]
  choose d hd using fun b => hrange (c b) (hcp b)
  let dh : B →+ A₀ :=
    { toFun := d
      map_zero' := he (by rw [hd, map_zero, map_zero])
      map_add' := fun b b' => he (by rw [hd, map_add, map_add, hd, hd]) }
  obtain ⟨m0, hm0, huniq⟩ := hκ dh
  refine ⟨θ.symm m0, fun b => ?_, fun m' hm' => ?_⟩
  · rw [kappaT_apply, LinearEquiv.apply_symm_apply, hm0]; exact hd b
  · have h1 : θ m' = m0 := huniq _ (fun b => he (by rw [← kappaT_apply M B κ e θ, hm']; exact (hd b).symm))
    rw [← h1, LinearEquiv.symm_apply_apply]

include he in

theorem perfect_of_comp_injective (κ₀ : B →+ M →+ A₀) (κ₁ : B →+ M →+ A) (hcomp : ∀ b m, e (κ₀ b m) = κ₁ b m)
    (hκ₁ : ∀ c : B →+ A, ∃! m : M, ∀ b, κ₁ b m = c b) (c : B →+ A₀) : ∃! m : M, ∀ b, κ₀ b m = c b := by
  obtain ⟨m, hm, huniq⟩ := hκ₁ (e.comp c)
  refine ⟨m, fun b => he (by rw [hcomp, hm]; rfl), fun m' hm' => huniq m' (fun b => by rw [← hcomp, hm']; rfl)⟩

end kappaT
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

section kappaQ

variable {p : ℕ} [Fact p.Prime] (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
  (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p)
  (q : ℕ) [Fact q.Prime] (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

noncomputable def eSigma : Additive (AlgebraicClosure ℚ)ˣ →+ Additive (PadicAlgCl q)ˣ :=
  (MonoidHom.toAdditive (Units.map (padicEmbedding q : AlgebraicClosure ℚ →* PadicAlgCl q))).comp
    ((Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)).ρ σ).toAddMonoidHom

theorem toMul_eSigma (x : Additive (AlgebraicClosure ℚ)ˣ) :
    Additive.toMul (eSigma q σ x) = Units.map (padicEmbedding q : AlgebraicClosure ℚ →* PadicAlgCl q)
      (Additive.toMul ((Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)).ρ σ x)) := rfl

theorem toMul_eSigma_ofMul (u : (AlgebraicClosure ℚ)ˣ) :
    Additive.toMul (eSigma q σ (Additive.ofMul u)) = Units.map (padicEmbedding q : AlgebraicClosure ℚ →* PadicAlgCl q) (σ • u) := rfl

theorem coe_toMul_eSigma_ofMul (u : (AlgebraicClosure ℚ)ˣ) :
    ((Additive.toMul (eSigma q σ (Additive.ofMul u)) : (PadicAlgCl q)ˣ) : PadicAlgCl q) = padicEmbedding q (σ (u : AlgebraicClosure ℚ)) := rfl

theorem eSigma_injective : Function.Injective (eSigma q σ) := by
  intro x y h
  obtain ⟨u, rfl⟩ : ∃ u, Additive.ofMul u = x := ⟨Additive.toMul x, rfl⟩
  obtain ⟨v, rfl⟩ : ∃ v, Additive.ofMul v = y := ⟨Additive.toMul y, rfl⟩
  have h1 := congrArg (fun z => ((Additive.toMul z : (PadicAlgCl q)ˣ) : PadicAlgCl q)) h
  simp only [coe_toMul_eSigma_ofMul] at h1
  have h2 : (u : AlgebraicClosure ℚ) = v := σ.injective ((padicEmbedding q).toRingHom.injective h1)
  rw [Units.ext h2]

include hζ in
theorem eSigma_range (a : Additive (PadicAlgCl q)ˣ) (ha : p • a = 0) : ∃ x, eSigma q σ x = a := by
  haveI : NeZero p := ⟨p_ne_zero'⟩
  have hinj : Function.Injective (AddMonoidHom.toMultiplicative (eSigma q σ)) := fun x y h =>
    Additive.ofMul.injective (eSigma_injective q σ (congrArg Additive.ofMul h :))
  have hζ' : IsPrimitiveRoot (AddMonoidHom.toMultiplicative (eSigma q σ) (zetaU ζ hζ)) p :=
    (zetaU_prim ζ hζ).map_of_injective hinj
  have hap : (Additive.toMul a) ^ p = 1 := by
    have := congrArg Additive.toMul ha
    rwa [toMul_nsmul, toMul_zero] at this
  obtain ⟨i, -, hi⟩ := hζ'.eq_pow_of_mem_rootsOfUnity ((mem_rootsOfUnity p (Additive.toMul a)).mpr hap)
  refine ⟨i • Additive.ofMul (zetaU ζ hζ), ?_⟩
  rw [map_nsmul]
  have hi' := congrArg Additive.ofMul hi
  rw [ofMul_pow, ofMul_toMul] at hi'
  exact hi'

variable {Gd : Type} [Group Gd] (B : Rep ℤ Gd) (κ : B →+ M →+ Additive (AlgebraicClosure ℚ)ˣ)

noncomputable abbrev kappaQ : B →+ M →+ Additive (PadicAlgCl q)ˣ := kappaT M B κ (eSigma q σ) (rhoEquiv M σ⁻¹)

theorem toMul_kappaQ (b : B) (m : M) : Additive.toMul (kappaQ M q σ B κ b m) =
    Units.map (padicEmbedding q : AlgebraicClosure ℚ →* PadicAlgCl q)
      (Additive.toMul ((Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)).ρ σ (κ b (M.ρ σ⁻¹ m)))) := rfl

variable (hB : ∀ b : B, p • b = 0) (hκ : ∀ c : B →+ Additive (AlgebraicClosure ℚ)ˣ, ∃! m : M, ∀ b, κ b m = c b)

include hζ hB hκ in
theorem kappaQ_perfect (c : B →+ Additive (PadicAlgCl q)ˣ) : ∃! m : M, ∀ b, kappaQ M q σ B κ b m = c b :=
  kappaT_perfect M B κ (eSigma q σ) (rhoEquiv M σ⁻¹) (eSigma_injective q σ) (eSigma_range ζ hζ q σ) hB hκ c

end kappaQ
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

end Reduce95
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

namespace Reduce95
open ExtCitation
open scoped NumberField.PlaceDecomp

section kappaQeqv

variable {p : ℕ} [Fact p.Prime] (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
  (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F] (q : Nat.Primes)
  (B : Rep ℤ (↥F ≃ₐ[ℚ] ↥F)) (κ : B →+ M →+ Additive (AlgebraicClosure ℚ)ˣ)
  (hκeq : ∀ (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (b : B) (m : M),
    κ (B.ρ (AlgEquiv.restrictNormalHom ↥F γ) b) (M.ρ γ m) = (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)).ρ γ (κ b m))

local instance factPrimes' (q : Nat.Primes) : Fact ((q : ℕ)).Prime := ⟨q.2⟩

noncomputable abbrev kappaQF : B →+ M →+ Additive (PadicAlgCl q)ˣ := kappaQ M (q : ℕ) (sigmaQ F q) B κ

theorem eSigma_conj (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (τ : primeLocalGaloisGroup q) (u : Additive (AlgebraicClosure ℚ)ˣ) :
    eSigma (q : ℕ) σ ((Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)).ρ (σ⁻¹ * primeLocalToGlobal q τ * σ) u) =
      (Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)).ρ (show PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q from τ) (eSigma (q : ℕ) σ u) := by
  obtain ⟨u, rfl⟩ : ∃ v, Additive.ofMul v = u := ⟨Additive.toMul u, rfl⟩
  change eSigma (q : ℕ) σ ((Rep.ofMulDistribMulAction _ _).ρ _ (Additive.ofMul u)) =
    (Rep.ofMulDistribMulAction _ _).ρ _ (eSigma (q : ℕ) σ (Additive.ofMul u))
  rw [Rep.ofMulDistribMulAction_ρ_apply_apply, Rep.ofMulDistribMulAction_ρ_apply_apply]
  apply Additive.toMul.injective
  apply Units.ext
  change padicEmbedding q (σ ((σ⁻¹ * primeLocalToGlobal q τ * σ) (u : AlgebraicClosure ℚ))) =
    (show PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q from τ) (padicEmbedding q (σ (u : AlgebraicClosure ℚ)))
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, ← AlgEquiv.mul_apply σ σ⁻¹, mul_inv_cancel, AlgEquiv.one_apply]
  exact padicEmbedding_localGaloisToGlobal q _ _

include hκeq in
theorem kappaQF_eqv (τ : primeLocalGaloisGroup q) (b : B) (m : M) :
    kappaQF M F q B κ (B.ρ ((piQ F q τ : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F (wq F q))) : ↥F ≃ₐ[ℚ] ↥F) b)
        (M.ρ (primeLocalToGlobal q τ) m) =
      (Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)).ρ (show PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q from τ) (kappaQF M F q B κ b m) := by
  rw [kappaT_apply, kappaT_apply, rhoEquiv_apply, rhoEquiv_apply, hpi_q]
  have h1 : M.ρ (sigmaQ F q)⁻¹ (M.ρ (primeLocalToGlobal q τ) m) =
      M.ρ ((sigmaQ F q)⁻¹ * primeLocalToGlobal q τ * sigmaQ F q) (M.ρ (sigmaQ F q)⁻¹ m) := by
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    congr 2; group
  rw [h1, hκeq]
  exact eSigma_conj q (sigmaQ F q) τ _

end kappaQeqv
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

end Reduce95
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

namespace Reduce95
open ExtCitation groupCohomology
open scoped NumberField.PlaceDecomp

section LamQ

variable {p : ℕ} [Fact p.Prime] (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) [FiniteDimensional (ZMod p) M]
  (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p)
  (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F]
  (hFM' : ∀ s ∈ F.fixingSubgroup, ∀ m : M.dualTwist (cycloChar p), (M.dualTwist (cycloChar p)).ρ s m = m)
  (q : Nat.Primes)

local instance factPrimes'' (q : Nat.Primes) : Fact ((q : ℕ)).Prime := ⟨q.2⟩

noncomputable abbrev DQ : Subgroup (↥F ≃ₐ[ℚ] ↥F) := NumberField.PlaceDecomp.decomp ℚ ↥F (wq F q)

noncomputable abbrev XQ : Rep ℤ ↥(DQ F q) := Rep.ofMulDistribMulAction ↥(DQ F q) ((wq F q).adicCompletion ↥F)ˣ

noncomputable abbrev kapF : Bof M F →+ M →+ Additive (AlgebraicClosure ℚ)ˣ := kappa M ζ hζ (Bof M F) (betaOf M F)
noncomputable abbrev kapQF : Bof M F →+ M →+ Additive (PadicAlgCl q)ˣ := kappaQF M F q (Bof M F) (kapF M ζ hζ F)

theorem kapF_eqv : ∀ (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (b : Bof M F) (m : M),
    kapF M ζ hζ F ((Bof M F).ρ (AlgEquiv.restrictNormalHom ↥F γ) b) (M.ρ γ m) =
      (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)).ρ γ (kapF M ζ hζ F b m) :=
  kappa_equivariant M ζ hζ (AlgEquiv.restrictNormalHom ↥F) (Bof M F) (betaOf M F) (betaOf_equivariant M F)

include hFM' in
theorem kapF_perfect : ∀ c : Bof M F →+ Additive (AlgebraicClosure ℚ)ˣ, ∃! m : M, ∀ b, kapF M ζ hζ F b m = c b :=
  kappa_perfect M ζ hζ (Bof M F) (betaOf M F) (betaOf_bijective M F hFM') (Bof_torsion M F)

include hFM' in
theorem exists_LamQ : ∃ Λ : (Rep.res (DQ F q).subtype (RB M F) ⟶ XQ F q) →+ H1 (Rep.res (primeLocalToGlobal q) M),
      IsLocalBridge₁ (piQ F q) ((Rep.resFunctor (DQ F q).subtype).map (Rep.relationModuleInt.ι (Bof M F)))
        ((Rep.resFunctor (DQ F q).subtype).map (Rep.freeCover (Bof M F)))
        (X := XQ F q)
        (A := (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)))
        (Units.map (PhiQ F q : (wq F q).adicCompletion ↥F →* PadicAlgCl q)).toAdditive (M := Rep.res (primeLocalToGlobal q) M) (kapQF M ζ hζ F q) Λ ∧
      (∀ φ, Λ φ = 0 ↔ ∃ χ : Rep.res (DQ F q).subtype (Rep.free ℤ (↥F ≃ₐ[ℚ] ↥F) (Bof M F)) ⟶ XQ F q,
        (Rep.resFunctor (DQ F q).subtype).map (Rep.relationModuleInt.ι (Bof M F)) ≫ χ = φ) ∧
      (∀ φ, Λ φ ∈ continuousH1 (primeLocalToGlobal q) (Rep.res (primeLocalToGlobal q) M)) ∧
      (∀ y ∈ continuousH1 (primeLocalToGlobal q) (Rep.res (primeLocalToGlobal q) M), ∃ φ, Λ φ = y) :=
  NumberField.PlaceDecomp.exists_isLocalBridge1_padicAlgCl q M F (wq F q) (sigmaQ F q) (PhiQ F q) (hPhiF_q F q) (hcont_q F q)
    (piQ F q) (hpi_q F q) (hpisurj_q F q) (heqv_q F q)
    (Rep.relationModuleInt.ι (Bof M F)) (Rep.freeCover (Bof M F))
    (relationModuleInt_ι_injective (Bof M F)) (exact_ι_freeCover (Bof M F)) (freeCover_surjective (Bof M F))
    (Bof M F) (Iso.refl _) (Bof_torsion M F)
    (kapQF M ζ hζ F q) (kappaQF_eqv M F q (Bof M F) (kapF M ζ hζ F) (kapF_eqv M ζ hζ F))
    (kappaQ_perfect M ζ hζ (q : ℕ) (sigmaQ F q) (Bof M F) (kapF M ζ hζ F) (Bof_torsion M F) (kapF_perfect M ζ hζ F hFM'))

noncomputable def LamQ : (Rep.res (DQ F q).subtype (RB M F) ⟶ XQ F q) →+ H1 (Rep.res (primeLocalToGlobal q) M) :=
  (exists_LamQ M ζ hζ F hFM' q).choose

def LamQ_spec := (exists_LamQ M ζ hζ F hFM' q).choose_spec

def LamQ_bridge := (LamQ_spec M ζ hζ F hFM' q).1
theorem LamQ_ker : ∀ φ, LamQ M ζ hζ F hFM' q φ = 0 ↔ ∃ χ : Rep.res (DQ F q).subtype (Rep.free ℤ (↥F ≃ₐ[ℚ] ↥F) (Bof M F)) ⟶ XQ F q,
    (Rep.resFunctor (DQ F q).subtype).map (Rep.relationModuleInt.ι (Bof M F)) ≫ χ = φ := (LamQ_spec M ζ hζ F hFM' q).2.1
theorem LamQ_mem : ∀ φ, LamQ M ζ hζ F hFM' q φ ∈ continuousH1 (primeLocalToGlobal q) (Rep.res (primeLocalToGlobal q) M) :=
  (LamQ_spec M ζ hζ F hFM' q).2.2.1
theorem LamQ_surj : ∀ y ∈ continuousH1 (primeLocalToGlobal q) (Rep.res (primeLocalToGlobal q) M), ∃ φ, LamQ M ζ hζ F hFM' q φ = y :=
  (LamQ_spec M ζ hζ F hFM' q).2.2.2

noncomputable def LamQc : (Rep.res (DQ F q).subtype (RB M F) ⟶ XQ F q) →+ ↥(continuousH1 (primeLocalToGlobal q) (Rep.res (primeLocalToGlobal q) M)) :=
  (LamQ M ζ hζ F hFM' q).codRestrict (continuousH1 (primeLocalToGlobal q) (Rep.res (primeLocalToGlobal q) M)).toAddSubgroup (LamQ_mem M ζ hζ F hFM' q)

@[scoped simp] theorem coe_LamQc (φ) : (LamQc M ζ hζ F hFM' q φ : H1 (Rep.res (primeLocalToGlobal q) M)) = LamQ M ζ hζ F hFM' q φ := rfl

theorem LamQc_surjective : Function.Surjective (LamQc M ζ hζ F hFM' q) := by
  intro y; obtain ⟨φ, hφ⟩ := LamQ_surj M ζ hζ F hFM' q y.1 y.2; exact ⟨φ, Subtype.ext hφ⟩

theorem LamQc_ker (φ) : LamQc M ζ hζ F hFM' q φ = 0 ↔ ∃ χ : Rep.res (DQ F q).subtype (Rep.free ℤ (↥F ≃ₐ[ℚ] ↥F) (Bof M F)) ⟶ XQ F q,
    (Rep.resFunctor (DQ F q).subtype).map (Rep.relationModuleInt.ι (Bof M F)) ≫ χ = φ := by
  rw [← LamQ_ker M ζ hζ F hFM' q]
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

end LamQ
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

end Reduce95
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

namespace Reduce95
open ExtCitation groupCohomology
open scoped NumberField.InfPlaceDecomp

section powZ
variable {p : ℕ} [Fact p.Prime] {R : Type} [Monoid R] (u : Rˣ) (hu : u ^ p = 1)

def powZ : ZMod p →+ Additive Rˣ where
  toFun a := Additive.ofMul (u ^ a.val)
  map_zero' := by rw [ZMod.val_zero, pow_zero]; rfl
  map_add' a b := by
    rw [← ofMul_mul, ← pow_add, ZMod.val_add, ← pow_eq_pow_mod _ hu]

theorem toMul_powZ (a : ZMod p) : Additive.toMul (powZ u hu a) = u ^ a.val := rfl

end powZ
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

section arch

variable {p : ℕ} [Fact p.Prime] (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
  (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p)
  (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F]
  (hζF : ζ ∈ F)

noncomputable def zetaF : (↥F)ˣ :=
  Units.mk0 ⟨ζ, hζF⟩ (fun h => (hζ.ne_zero p_ne_zero') (congrArg Subtype.val h :))

theorem coe_zetaF : ((zetaF ζ hζ F hζF : (↥F)ˣ) : ↥F) = ⟨ζ, hζF⟩ := rfl

theorem map_zetaF : Units.map (algebraMap ↥F (AlgebraicClosure ℚ) : ↥F →* AlgebraicClosure ℚ) (zetaF ζ hζ F hζF) = zetaU ζ hζ :=
  Units.ext (by rw [Units.coe_map, coe_zetaU]; rfl)

theorem zetaF_pow_p : zetaF ζ hζ F hζF ^ p = 1 := by
  have hinj : Function.Injective (Units.map (algebraMap ↥F (AlgebraicClosure ℚ) : ↥F →* AlgebraicClosure ℚ)) := by
    intro x y h; apply Units.ext; apply (algebraMap ↥F (AlgebraicClosure ℚ)).injective; exact congrArg (fun u : (AlgebraicClosure ℚ)ˣ => (u : AlgebraicClosure ℚ)) h
  apply hinj; rw [map_pow, map_zetaF, map_one]; exact zetaU_pow_p ζ hζ

theorem zetaF_prim : IsPrimitiveRoot (zetaF ζ hζ F hζF) p := by
  have h := zetaU_prim ζ hζ
  rw [← map_zetaF ζ hζ F hζF] at h
  exact h.of_map_of_injective (by
    intro x y hxy; apply Units.ext; apply (algebraMap ↥F (AlgebraicClosure ℚ)).injective
    exact congrArg (fun u : (AlgebraicClosure ℚ)ˣ => (u : AlgebraicClosure ℚ)) hxy)

variable {Gd : Type} [Group Gd] (B : Rep ℤ Gd) (β : B →+ M.dualTwist (cycloChar p))

noncomputable def kappaF : B →+ M →+ Additive (↥F)ˣ where
  toFun b := (powZ (zetaF ζ hζ F hζF) (zetaF_pow_p ζ hζ F hζF)).comp ((β b : M.dualTwist (cycloChar p)) : Module.Dual (ZMod p) M).toAddMonoidHom
  map_zero' := by ext m; simp
  map_add' b b' := by ext m; simp

noncomputable abbrev eF : Additive (↥F)ˣ →+ Additive (AlgebraicClosure ℚ)ˣ :=
  (Units.map (algebraMap ↥F (AlgebraicClosure ℚ) : ↥F →* AlgebraicClosure ℚ)).toAdditive

theorem eF_injective : Function.Injective (eF F) := by
  intro x y h; apply Additive.toMul.injective; apply Units.ext; apply (algebraMap ↥F (AlgebraicClosure ℚ)).injective
  exact congrArg (fun u : (AlgebraicClosure ℚ)ˣ => (u : AlgebraicClosure ℚ)) (congrArg Additive.toMul h)

theorem eF_kappaF (b : B) (m : M) : eF F (kappaF M ζ hζ F hζF B β b m) = kappa M ζ hζ B β b m := by
  change Additive.ofMul (Units.map (algebraMap ↥F (AlgebraicClosure ℚ) : ↥F →* AlgebraicClosure ℚ) (zetaF ζ hζ F hζF ^ _)) = Additive.ofMul (zetaU ζ hζ ^ _)
  rw [map_pow, map_zetaF]

end arch
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

end Reduce95
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

namespace Reduce95
open ExtCitation groupCohomology
open scoped NumberField.InfPlaceDecomp

section archCoords

variable (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F] [IsTotallyComplex ↥F]

noncomputable abbrev winf : InfinitePlace ↥F := NumberField.ArchIdele.above ℚ ↥F default

def coordsInf := NumberField.InfPlaceDecomp.exists_restrictNormalHom_conj_complexConjugation_mem_decomp F (winf F)

noncomputable def sigmaInf : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ := (coordsInf F).choose
def sigmaInf_spec := (coordsInf F).choose_spec

noncomputable abbrev cSig : ↥F ≃ₐ[ℚ] ↥F := AlgEquiv.restrictNormalHom ↥F ((sigmaInf F)⁻¹ * complexConjugation * sigmaInf F)

theorem cSig_mem : cSig F ∈ NumberField.InfPlaceDecomp.decomp ℚ ↥F (winf F) := (sigmaInf_spec F).1
theorem cSig_ne_one : cSig F ≠ 1 := (sigmaInf_spec F).2.1
theorem decomp_inf_cases : ∀ d : ↥(NumberField.InfPlaceDecomp.decomp ℚ ↥F (winf F)), (d : ↥F ≃ₐ[ℚ] ↥F) = 1 ∨ (d : ↥F ≃ₐ[ℚ] ↥F) = cSig F :=
  (sigmaInf_spec F).2.2.1
theorem hσF_inf : (sigmaInf F)⁻¹ * complexConjugation * sigmaInf F ∉ F.fixingSubgroup := (sigmaInf_spec F).2.2.2

theorem complexConjugation_zpow_two : complexConjugation ^ (2 : ℤ) = 1 := by
  rw [show ((2 : ℤ)) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast]; exact complexConjugation_sq

theorem archDecomp_cases (h : ↥archimedeanDecomposition) :
    (h : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) = 1 ∨ (h : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) = complexConjugation := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h.2
  rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · left
    rw [← hk, show (m + m : ℤ) = 2 * m by ring, zpow_mul, complexConjugation_zpow_two, one_zpow]
  · right
    rw [← hk, zpow_add, zpow_one, zpow_mul, complexConjugation_zpow_two, one_zpow, one_mul]

noncomputable def piInf : ↥archimedeanDecomposition →* ↥(NumberField.InfPlaceDecomp.decomp ℚ ↥F (winf F)) where
  toFun h := ⟨AlgEquiv.restrictNormalHom ↥F ((sigmaInf F)⁻¹ * (h : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) * sigmaInf F), by
    rcases archDecomp_cases h with h1 | hc
    · rw [h1, mul_one, inv_mul_cancel, map_one]; exact one_mem _
    · rw [hc]; exact cSig_mem F⟩
  map_one' := Subtype.ext (by simp)
  map_mul' h h' := Subtype.ext (by
    change AlgEquiv.restrictNormalHom ↥F ((sigmaInf F)⁻¹ * ((h * h' : ↥archimedeanDecomposition) : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) * sigmaInf F) =
      AlgEquiv.restrictNormalHom ↥F ((sigmaInf F)⁻¹ * (h : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) * sigmaInf F) *
        AlgEquiv.restrictNormalHom ↥F ((sigmaInf F)⁻¹ * (h' : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) * sigmaInf F)
    rw [← map_mul (AlgEquiv.restrictNormalHom ↥F), Subgroup.coe_mul]
    congr 1
    group)

theorem hpi_inf : ∀ h : ↥archimedeanDecomposition, ((piInf F h : ↥(NumberField.InfPlaceDecomp.decomp ℚ ↥F (winf F))) : ↥F ≃ₐ[ℚ] ↥F) =
    AlgEquiv.restrictNormalHom ↥F ((sigmaInf F)⁻¹ * (h : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) * sigmaInf F) := fun _ => rfl

theorem piInf_one' (h : ↥archimedeanDecomposition) (h1 : (h : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) = 1) :
    ((piInf F h : ↥(NumberField.InfPlaceDecomp.decomp ℚ ↥F (winf F))) : ↥F ≃ₐ[ℚ] ↥F) = 1 := by
  rw [hpi_inf, h1, mul_one, inv_mul_cancel, map_one]

theorem piInf_c (h : ↥archimedeanDecomposition) (hc : (h : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) = complexConjugation) :
    ((piInf F h : ↥(NumberField.InfPlaceDecomp.decomp ℚ ↥F (winf F))) : ↥F ≃ₐ[ℚ] ↥F) = cSig F := by
  rw [hpi_inf, hc]

theorem piInf_bijective : Function.Bijective (piInf F) := by
  constructor
  · intro h h' e
    have e' := congrArg (fun d : ↥(NumberField.InfPlaceDecomp.decomp ℚ ↥F (winf F)) => (d : ↥F ≃ₐ[ℚ] ↥F)) e
    beta_reduce at e'
    apply Subtype.ext
    rcases archDecomp_cases h with h1 | hc <;> rcases archDecomp_cases h' with h1' | hc'
    · rw [h1, h1']
    · exfalso; apply cSig_ne_one F; rw [piInf_one' F h h1, piInf_c F h' hc'] at e'; exact e'.symm
    · exfalso; apply cSig_ne_one F; rw [piInf_c F h hc, piInf_one' F h' h1'] at e'; exact e'
    · rw [hc, hc']
  · intro d
    rcases decomp_inf_cases F d with h1 | hc
    · exact ⟨1, Subtype.ext (by rw [map_one]; exact h1.symm)⟩
    · exact ⟨archimedeanGen, Subtype.ext (by rw [hc]; rfl)⟩

end archCoords
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

section kappaInf

variable {p : ℕ} [Fact p.Prime] (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) [FiniteDimensional (ZMod p) M]
  (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p)
  (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F] [IsTotallyComplex ↥F]
  (hζF : ζ ∈ F)
  (B : Rep ℤ (↥F ≃ₐ[ℚ] ↥F)) (β : B →+ M.dualTwist (cycloChar p))
  (hβeq : ∀ (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (b : B),
    β (B.ρ (AlgEquiv.restrictNormalHom ↥F γ) b) = (M.dualTwist (cycloChar p)).ρ γ (β b))
  (hβ : Function.Bijective β) (hB : ∀ b : B, p • b = 0)

noncomputable abbrev eInf : Additive (↥F)ˣ →+ Additive ((winf F).Completion)ˣ :=
  (Units.map (NumberField.SIdele.locInf ℚ ↥F default).toMonoidHom).toAdditive

theorem eInf_injective : Function.Injective (eInf F) := by
  intro x y h; apply Additive.toMul.injective; apply Units.ext; apply (NumberField.SIdele.locInf ℚ ↥F default).injective
  exact congrArg (fun u : ((winf F).Completion)ˣ => (u : (winf F).Completion)) (congrArg Additive.toMul h)

include hζ hζF in
theorem eInf_range (a : Additive ((winf F).Completion)ˣ) (ha : p • a = 0) : ∃ x, eInf F x = a := by
  haveI : NeZero p := ⟨p_ne_zero'⟩
  have hinj : Function.Injective (AddMonoidHom.toMultiplicative (eInf F)) := fun x y h =>
    Additive.ofMul.injective (eInf_injective F (congrArg Additive.ofMul h :))
  have hζ' : IsPrimitiveRoot (AddMonoidHom.toMultiplicative (eInf F) (zetaF ζ hζ F hζF)) p :=
    (zetaF_prim ζ hζ F hζF).map_of_injective hinj
  have hap : (Additive.toMul a) ^ p = 1 := by
    have := congrArg Additive.toMul ha
    rwa [toMul_nsmul, toMul_zero] at this
  obtain ⟨i, -, hi⟩ := hζ'.eq_pow_of_mem_rootsOfUnity ((mem_rootsOfUnity p (Additive.toMul a)).mpr hap)
  refine ⟨i • Additive.ofMul (zetaF ζ hζ F hζF), ?_⟩
  rw [map_nsmul]
  have hi' := congrArg Additive.ofMul hi
  rw [ofMul_pow, ofMul_toMul] at hi'
  exact hi'

noncomputable abbrev kappaInf : B →+ M →+ Additive ((winf F).Completion)ˣ :=
  kappaT M B (kappaF M ζ hζ F hζF B β) (eInf F) (rhoEquiv M (sigmaInf F)⁻¹)

include hβ hB in
theorem kappaInf_perfect (c : B →+ Additive ((winf F).Completion)ˣ) : ∃! m : M, ∀ b, kappaInf M ζ hζ F hζF B β b m = c b :=
  kappaT_perfect M B (kappaF M ζ hζ F hζF B β) (eInf F) (rhoEquiv M (sigmaInf F)⁻¹) (eInf_injective F) (eInf_range ζ hζ F hζF) hB
    (perfect_of_comp_injective M B (eF F) (eF_injective F) (kappaF M ζ hζ F hζF B β) (kappa M ζ hζ B β)
      (eF_kappaF M ζ hζ F hζF B β) (kappa_perfect M ζ hζ B β hβ hB)) c

include hβeq in

theorem kappaF_eqv (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (b : B) (m : M) :
    kappaF M ζ hζ F hζF B β (B.ρ (AlgEquiv.restrictNormalHom ↥F γ) b) (M.ρ γ m) =
      (Rep.ofAlgebraAutOnUnits ℚ ↥F).ρ (AlgEquiv.restrictNormalHom ↥F γ) (kappaF M ζ hζ F hζF B β b m) := by
  apply eF_injective F
  rw [eF_kappaF, kappa_equivariant M ζ hζ (AlgEquiv.restrictNormalHom ↥F) B β hβeq, ← eF_kappaF M ζ hζ F hζF B β]
  generalize kappaF M ζ hζ F hζF B β b m = u
  obtain ⟨u, rfl⟩ : ∃ v, Additive.ofMul v = u := ⟨Additive.toMul u, rfl⟩
  change (Rep.ofMulDistribMulAction _ _).ρ γ (eF F (Additive.ofMul u)) = eF F ((Rep.ofMulDistribMulAction _ _).ρ _ (Additive.ofMul u))
  rw [Rep.ofMulDistribMulAction_ρ_apply_apply, Rep.ofMulDistribMulAction_ρ_apply_apply]
  apply Additive.toMul.injective
  apply Units.ext
  change γ (algebraMap ↥F (AlgebraicClosure ℚ) (u : ↥F)) = algebraMap ↥F (AlgebraicClosure ℚ) ((AlgEquiv.restrictNormalHom ↥F γ) (u : ↥F))
  exact (AlgEquiv.restrictNormal_commutes γ ↥F _).symm

set_option maxHeartbeats 3200000 in
include hβeq in
theorem kappaInf_eqv (h : ↥archimedeanDecomposition) (b : B) (m : M) :
    kappaInf M ζ hζ F hζF B β (B.ρ ((piInf F h : ↥(NumberField.InfPlaceDecomp.decomp ℚ ↥F (winf F))) : ↥F ≃ₐ[ℚ] ↥F) b)
        (M.ρ (h : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) m) =
      (NumberField.InfPlaceDecomp.localUnits ℚ ↥F (winf F)).ρ (piInf F h) (kappaInf M ζ hζ F hζF B β b m) := by
  rw [kappaT_apply, kappaT_apply, rhoEquiv_apply, rhoEquiv_apply, hpi_inf]
  have h1 : M.ρ (sigmaInf F)⁻¹ (M.ρ (h : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) m) =
      M.ρ ((sigmaInf F)⁻¹ * (h : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) * sigmaInf F) (M.ρ (sigmaInf F)⁻¹ m) := by
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    congr 2; group
  rw [h1]
  rw [kappaF_eqv M ζ hζ F hζF B β hβeq ((sigmaInf F)⁻¹ * (h : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) * sigmaInf F) b (M.ρ (sigmaInf F)⁻¹ m)]
  generalize kappaF M ζ hζ F hζF B β b (M.ρ (sigmaInf F)⁻¹ m) = u
  obtain ⟨u, rfl⟩ : ∃ v, Additive.ofMul v = u := ⟨Additive.toMul u, rfl⟩
  change eInf F ((Rep.ofMulDistribMulAction _ _).ρ _ (Additive.ofMul u)) = (Rep.ofMulDistribMulAction _ _).ρ _ (eInf F (Additive.ofMul u))
  rw [Rep.ofMulDistribMulAction_ρ_apply_apply, Rep.ofMulDistribMulAction_ρ_apply_apply]
  apply Additive.toMul.injective
  apply Units.ext
  change NumberField.SIdele.locInf ℚ ↥F default ((piInf F h : ↥F ≃ₐ[ℚ] ↥F) (u : ↥F)) =
    ((piInf F h • Units.map (NumberField.SIdele.locInf ℚ ↥F default).toMonoidHom u : ((winf F).Completion)ˣ) : (winf F).Completion)
  rw [NumberField.InfPlaceDecomp.coe_smul_units, Units.coe_map]
  exact (NumberField.SIdele.smul_locInf ℚ ↥F default (piInf F h) (u : ↥F)).symm

end kappaInf
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

end Reduce95
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

namespace Reduce95
open ExtCitation groupCohomology GroupCohomology M4aHerbrand
open scoped NumberField.PlaceDecomp

section levelPrimed

variable {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
  (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) [FiniteDimensional (ZMod p) M]
  (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p)
  (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F]
  (hFS : F.IsUnramifiedOutside S)
  (B : Rep ℤ (↥F ≃ₐ[ℚ] ↥F)) [Fintype B] (β : B →+ M.dualTwist (cycloChar p))
  (hβeq : ∀ (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (b : B),
    β (B.ρ (AlgEquiv.restrictNormalHom ↥F γ) b) = (M.dualTwist (cycloChar p)).ρ γ (β b))
  (hβ : Function.Bijective β) (hB : ∀ b : B, p • b = 0)

scoped instance moduleFree_relationCarrier' : Module.Free ℤ (Rep.relationCarrier B) := by
  haveI : Fintype (↥F ≃ₐ[ℚ] ↥F) := Fintype.ofFinite _
  exact Rep.moduleFree_relationCarrier B

theorem hT' : ((seqF S F).map (ihom (Rep.relationModuleInt B))).ShortExact :=
  Rep.shortExact_map_ihom_of_free (Rep.relationCarrier B) (Rep.relationRepInt B) (seqF_shortExact S F)

noncomputable def dY' : (Rep.relationModuleInt B ⟶ (seqF S F).X₃) →+ H1 ((ihom (Rep.relationModuleInt B)).obj (seqF S F).X₁) :=
  ((groupCohomology.δ (hT' S F B) 0 1 rfl).hom.toAddMonoidHom.comp
    (groupCohomology.H0Iso ((ihom (Rep.relationModuleInt B)).obj (seqF S F).X₃)).inv.hom.toAddMonoidHom).comp
    (Representation.linHom.invariantsEquivRepHom (Rep.relationModuleInt B) (seqF S F).X₃).symm.toLinearMap.toAddMonoidHom

theorem dY'_apply (t : Rep.relationModuleInt B ⟶ (seqF S F).X₃) : dY' S F B t = (groupCohomology.δ (hT' S F B) 0 1 rfl).hom
    ((groupCohomology.H0Iso ((ihom (Rep.relationModuleInt B)).obj (seqF S F).X₃)).inv
      ((Representation.linHom.invariantsEquivRepHom (Rep.relationModuleInt B) (seqF S F).X₃).symm t)) := rfl

theorem hLESa' (x : H1 ((ihom (Rep.relationModuleInt B)).obj (seqF S F).X₁))
    (hx : (groupCohomology.map (MonoidHom.id _) ((ihom (Rep.relationModuleInt B)).map (seqF S F).f) 1).hom x = 0) : ∃ t, dY' S F B t = x :=
  Rep.exists_delta_hom_eq_of_map_ihom_map_eq_zero (Rep.relationModuleInt B) (hT' S F B) x hx

theorem hLESb' (t : Rep.relationModuleInt B ⟶ (seqF S F).X₃) (ht : dY' S F B t = 0) :
    ∃ s : Rep.relationModuleInt B ⟶ (seqF S F).X₂, t = s ≫ (seqF S F).g :=
  Rep.exists_eq_comp_of_delta_hom_eq_zero (Rep.relationModuleInt B) (hT' S F B) t ht

theorem hLESc' (s : Rep.relationModuleInt B ⟶ (seqF S F).X₂) : dY' S F B (s ≫ (seqF S F).g) = 0 :=
  Rep.delta_hom_comp_eq_zero (Rep.relationModuleInt B) (hT' S F B) s

theorem torsion_of_smul (b : B) : p • b = 0 → p • b = 0 := id

def hdiv' := NumberField.SUnits.exists_ihom_extension_fixed_of_sLevel_of_injective S hpS (Sq S) (coe_Sq S) F hFS
    (Rep.relationModuleInt.ι B) (Rep.freeCover B) (relationModuleInt_ι_injective B) (exact_ι_freeCover B)
    (freeCover_surjective B) hB (iotaE F (Sq S)) (toMul_iotaE F (Sq S))

include hpS hFS hβeq hβ hB in

theorem exists_LE2' : ∃ Λ : H1 ((ihom (Rep.relationModuleInt B)).obj (NumberField.SUnits.sUnitsRep ℚ ↥F (Sq S))) →+ continuousH2S S M,
    IsGlobalBridge₂ S (AlgEquiv.restrictNormalHom ↥F) (Rep.relationModuleInt.ι B) (Rep.freeCover B)
      (A := Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)) (iotaE F (Sq S)) (kappa M ζ hζ B β) Λ :=
  groupCohomology.exists_isGlobalBridge2 S (AlgEquiv.restrictNormalHom ↥F) (hπlev_F S F hFS)
    (Rep.relationModuleInt.ι B) (Rep.freeCover B) (exact_ι_freeCover B) (freeCover_surjective B)
    (X := NumberField.SUnits.sUnitsRep ℚ ↥F (Sq S)) (A := Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ))
    (iotaE F (Sq S)) (iotaE_injective F (Sq S)) (iotaE_equivariant F (Sq S))
    (p := p) (M := M) (kappa M ζ hζ B β) (kappa_equivariant M ζ hζ (AlgEquiv.restrictNormalHom ↥F) B β hβeq)
    (kappa_perfect M ζ hζ B β hβ hB) (hdiv' S hpS F hFS B hB)

noncomputable def LE2' : H1 ((ihom (Rep.relationModuleInt B)).obj (NumberField.SUnits.sUnitsRep ℚ ↥F (Sq S))) →+ continuousH2S S M :=
  (exists_LE2' S hpS M ζ hζ F hFS B β hβeq hβ hB).choose

include hpS hFS hβeq hβ hB in
theorem LE2'_spec : IsGlobalBridge₂ S (AlgEquiv.restrictNormalHom ↥F) (Rep.relationModuleInt.ι B) (Rep.freeCover B)
      (A := Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)) (iotaE F (Sq S)) (kappa M ζ hζ B β) (LE2' S hpS M ζ hζ F hFS B β hβeq hβ hB) :=
  (exists_LE2' S hpS M ζ hζ F hFS B β hβeq hβ hB).choose_spec

variable (q : Nat.Primes)
local instance factPrimesP (q : Nat.Primes) : Fact ((q : ℕ)).Prime := ⟨q.2⟩

include hβeq hβ hB in
theorem exists_LamQ' : ∃ Λ : (Rep.res (DQ F q).subtype (Rep.relationModuleInt B) ⟶ XQ F q) →+ H1 (Rep.res (primeLocalToGlobal q) M),
      IsLocalBridge₁ (piQ F q) ((Rep.resFunctor (DQ F q).subtype).map (Rep.relationModuleInt.ι B))
        ((Rep.resFunctor (DQ F q).subtype).map (Rep.freeCover B))
        (X := XQ F q)
        (A := (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)))
        (Units.map (PhiQ F q : (wq F q).adicCompletion ↥F →* PadicAlgCl q)).toAdditive (M := Rep.res (primeLocalToGlobal q) M)
        (kappaQF M F q B (kappa M ζ hζ B β)) Λ ∧
      (∀ φ, Λ φ = 0 ↔ ∃ χ : Rep.res (DQ F q).subtype (Rep.free ℤ (↥F ≃ₐ[ℚ] ↥F) B) ⟶ XQ F q,
        (Rep.resFunctor (DQ F q).subtype).map (Rep.relationModuleInt.ι B) ≫ χ = φ) ∧
      (∀ φ, Λ φ ∈ continuousH1 (primeLocalToGlobal q) (Rep.res (primeLocalToGlobal q) M)) ∧
      (∀ y ∈ continuousH1 (primeLocalToGlobal q) (Rep.res (primeLocalToGlobal q) M), ∃ φ, Λ φ = y) := by
  haveI : Finite B := inferInstance
  exact NumberField.PlaceDecomp.exists_isLocalBridge1_padicAlgCl q M F (wq F q) (sigmaQ F q) (PhiQ F q) (hPhiF_q F q) (hcont_q F q)
    (piQ F q) (hpi_q F q) (hpisurj_q F q) (heqv_q F q)
    (Rep.relationModuleInt.ι B) (Rep.freeCover B)
    (relationModuleInt_ι_injective B) (exact_ι_freeCover B) (freeCover_surjective B)
    B (Iso.refl _) hB
    (kappaQF M F q B (kappa M ζ hζ B β))
    (kappaQF_eqv M F q B (kappa M ζ hζ B β) (kappa_equivariant M ζ hζ (AlgEquiv.restrictNormalHom ↥F) B β hβeq))
    (kappaQ_perfect M ζ hζ (q : ℕ) (sigmaQ F q) B (kappa M ζ hζ B β) hB (kappa_perfect M ζ hζ B β hβ hB))

noncomputable def LamQ' : (Rep.res (DQ F q).subtype (Rep.relationModuleInt B) ⟶ XQ F q) →+ H1 (Rep.res (primeLocalToGlobal q) M) :=
  (exists_LamQ' M ζ hζ F B β hβeq hβ hB q).choose

def LamQ'_spec := (exists_LamQ' M ζ hζ F B β hβeq hβ hB q).choose_spec

def LamQ'_bridge := (LamQ'_spec M ζ hζ F B β hβeq hβ hB q).1
theorem LamQ'_ker : ∀ φ, LamQ' M ζ hζ F B β hβeq hβ hB q φ = 0 ↔ ∃ χ : Rep.res (DQ F q).subtype (Rep.free ℤ (↥F ≃ₐ[ℚ] ↥F) B) ⟶ XQ F q,
    (Rep.resFunctor (DQ F q).subtype).map (Rep.relationModuleInt.ι B) ≫ χ = φ := (LamQ'_spec M ζ hζ F B β hβeq hβ hB q).2.1
theorem LamQ'_mem : ∀ φ, LamQ' M ζ hζ F B β hβeq hβ hB q φ ∈ continuousH1 (primeLocalToGlobal q) (Rep.res (primeLocalToGlobal q) M) :=
  (LamQ'_spec M ζ hζ F B β hβeq hβ hB q).2.2.1
theorem LamQ'_surj : ∀ y ∈ continuousH1 (primeLocalToGlobal q) (Rep.res (primeLocalToGlobal q) M), ∃ φ, LamQ' M ζ hζ F B β hβeq hβ hB q φ = y :=
  (LamQ'_spec M ζ hζ F B β hβeq hβ hB q).2.2.2

noncomputable def LamQc' : (Rep.res (DQ F q).subtype (Rep.relationModuleInt B) ⟶ XQ F q) →+ ↥(continuousH1 (primeLocalToGlobal q) (Rep.res (primeLocalToGlobal q) M)) :=
  (LamQ' M ζ hζ F B β hβeq hβ hB q).codRestrict (continuousH1 (primeLocalToGlobal q) (Rep.res (primeLocalToGlobal q) M)).toAddSubgroup
    (LamQ'_mem M ζ hζ F B β hβeq hβ hB q)

@[scoped simp] theorem coe_LamQc' (φ) : (LamQc' M ζ hζ F B β hβeq hβ hB q φ : H1 (Rep.res (primeLocalToGlobal q) M)) = LamQ' M ζ hζ F B β hβeq hβ hB q φ := rfl

theorem LamQc'_surjective : Function.Surjective (LamQc' M ζ hζ F B β hβeq hβ hB q) := by
  intro y; obtain ⟨φ, hφ⟩ := LamQ'_surj M ζ hζ F B β hβeq hβ hB q y.1 y.2; exact ⟨φ, Subtype.ext hφ⟩

theorem LamQc'_ker (φ) : LamQc' M ζ hζ F B β hβeq hβ hB q φ = 0 ↔ ∃ χ : Rep.res (DQ F q).subtype (Rep.free ℤ (↥F ≃ₐ[ℚ] ↥F) B) ⟶ XQ F q,
    (Rep.resFunctor (DQ F q).subtype).map (Rep.relationModuleInt.ι B) ≫ χ = φ := by
  rw [← LamQ'_ker M ζ hζ F B β hβeq hβ hB q]
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

end levelPrimed
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

end Reduce95
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

namespace Reduce95
open ExtCitation groupCohomology GroupCohomology
open scoped NumberField.InfPlaceDecomp NumberField.PlaceDecomp

section LamInf

variable {p : ℕ} [Fact p.Prime] (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) [FiniteDimensional (ZMod p) M]
  (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p)
  (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F] [IsTotallyComplex ↥F]
  (hζF : ζ ∈ F)
  (B : Rep ℤ (↥F ≃ₐ[ℚ] ↥F)) [Fintype B] (β : B →+ M.dualTwist (cycloChar p))
  (hβeq : ∀ (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (b : B),
    β (B.ρ (AlgEquiv.restrictNormalHom ↥F γ) b) = (M.dualTwist (cycloChar p)).ρ γ (β b))
  (hβ : Function.Bijective β) (hB : ∀ b : B, p • b = 0)

noncomputable abbrev DInf : Subgroup (↥F ≃ₐ[ℚ] ↥F) := NumberField.InfPlaceDecomp.decomp ℚ ↥F (winf F)
noncomputable abbrev XInf : Rep ℤ ↥(DInf F) := NumberField.InfPlaceDecomp.localUnits ℚ ↥F (winf F)

include hβeq hβ hB in
theorem exists_LamInf : ∃ Λ : (Rep.res (DInf F).subtype (Rep.relationModuleInt B) ⟶ XInf F) →+ H1 (Rep.res archimedeanLoc M),
      IsLocalBridge₁ (piInf F) ((Rep.resFunctor (DInf F).subtype).map (Rep.relationModuleInt.ι B))
        ((Rep.resFunctor (DInf F).subtype).map (Rep.freeCover B))
        (A := Rep.res (piInf F) (XInf F))
        (AddMonoidHom.id (Additive ((winf F).Completion)ˣ)) (M := Rep.res archimedeanLoc M) (kappaInf M ζ hζ F hζF B β) Λ ∧
      (∀ φ, Λ φ = 0 ↔ ∃ χ : Rep.res (DInf F).subtype (Rep.free ℤ (↥F ≃ₐ[ℚ] ↥F) B) ⟶ XInf F,
        (Rep.resFunctor (DInf F).subtype).map (Rep.relationModuleInt.ι B) ≫ χ = φ) ∧
      (∀ φ, Λ φ ∈ continuousH1 archimedeanLoc (Rep.res archimedeanLoc M)) ∧
      (∀ y ∈ continuousH1 archimedeanLoc (Rep.res archimedeanLoc M), ∃ φ, Λ φ = y) := by
  haveI : Finite B := inferInstance
  exact NumberField.InfPlaceDecomp.exists_isLocalBridge1_archimedean M F (winf F) (sigmaInf F) (piInf F) (hpi_inf F) (piInf_bijective F)
    (hσF_inf F) (Rep.relationModuleInt.ι B) (Rep.freeCover B)
    (relationModuleInt_ι_injective B) (exact_ι_freeCover B) (freeCover_surjective B)
    B (Iso.refl _) hB (kappaInf M ζ hζ F hζF B β) (kappaInf_eqv M ζ hζ F hζF B β hβeq) (kappaInf_perfect M ζ hζ F hζF B β hβ hB)

noncomputable def LamInf : (Rep.res (DInf F).subtype (Rep.relationModuleInt B) ⟶ XInf F) →+ H1 (Rep.res archimedeanLoc M) :=
  (exists_LamInf M ζ hζ F hζF B β hβeq hβ hB).choose

def LamInf_spec := (exists_LamInf M ζ hζ F hζF B β hβeq hβ hB).choose_spec
def LamInf_bridge := (LamInf_spec M ζ hζ F hζF B β hβeq hβ hB).1
theorem LamInf_ker : ∀ φ, LamInf M ζ hζ F hζF B β hβeq hβ hB φ = 0 ↔ ∃ χ : Rep.res (DInf F).subtype (Rep.free ℤ (↥F ≃ₐ[ℚ] ↥F) B) ⟶ XInf F,
    (Rep.resFunctor (DInf F).subtype).map (Rep.relationModuleInt.ι B) ≫ χ = φ := (LamInf_spec M ζ hζ F hζF B β hβeq hβ hB).2.1
theorem LamInf_mem : ∀ φ, LamInf M ζ hζ F hζF B β hβeq hβ hB φ ∈ continuousH1 archimedeanLoc (Rep.res archimedeanLoc M) :=
  (LamInf_spec M ζ hζ F hζF B β hβeq hβ hB).2.2.1
theorem LamInf_surj : ∀ y ∈ continuousH1 archimedeanLoc (Rep.res archimedeanLoc M), ∃ φ, LamInf M ζ hζ F hζF B β hβeq hβ hB φ = y :=
  (LamInf_spec M ζ hζ F hζF B β hβeq hβ hB).2.2.2

noncomputable def LamInfc : (Rep.res (DInf F).subtype (Rep.relationModuleInt B) ⟶ XInf F) →+ ↥(continuousH1 archimedeanLoc (Rep.res archimedeanLoc M)) :=
  (LamInf M ζ hζ F hζF B β hβeq hβ hB).codRestrict (continuousH1 archimedeanLoc (Rep.res archimedeanLoc M)).toAddSubgroup
    (LamInf_mem M ζ hζ F hζF B β hβeq hβ hB)

@[scoped simp] theorem coe_LamInfc (φ) : (LamInfc M ζ hζ F hζF B β hβeq hβ hB φ : H1 (Rep.res archimedeanLoc M)) = LamInf M ζ hζ F hζF B β hβeq hβ hB φ := rfl

theorem LamInfc_surjective : Function.Surjective (LamInfc M ζ hζ F hζF B β hβeq hβ hB) := by
  intro y; obtain ⟨φ, hφ⟩ := LamInf_surj M ζ hζ F hζF B β hβeq hβ hB y.1 y.2; exact ⟨φ, Subtype.ext hφ⟩

theorem LamInfc_ker (φ) : LamInfc M ζ hζ F hζF B β hβeq hβ hB φ = 0 ↔ ∃ χ : Rep.res (DInf F).subtype (Rep.free ℤ (↥F ≃ₐ[ℚ] ↥F) B) ⟶ XInf F,
    (Rep.resFunctor (DInf F).subtype).map (Rep.relationModuleInt.ι B) ≫ χ = φ := by
  rw [← LamInf_ker M ζ hζ F hζF B β hβeq hβ hB]
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

end LamInf
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

section LJ1

variable {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes)
  (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) [FiniteDimensional (ZMod p) M]
  (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p)
  (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F] [IsTotallyComplex ↥F]
  (hζF : ζ ∈ F)
  (B : Rep ℤ (↥F ≃ₐ[ℚ] ↥F)) [Fintype B] (β : B →+ M.dualTwist (cycloChar p))
  (hβeq : ∀ (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (b : B),
    β (B.ρ (AlgEquiv.restrictNormalHom ↥F γ) b) = (M.dualTwist (cycloChar p)).ρ γ (β b))
  (hβ : Function.Bijective β) (hB : ∀ b : B, p • b = 0)

noncomputable def LamV : ∀ v : extArithIndex S,
    (Rep.res (Dv S F v).subtype (Rep.relationModuleInt B) ⟶ Yv S F v) →+ ↥(continuousH1 (extArithLoc S v) (Rep.res (extArithLoc S v) M))
  | Sum.inl _ => LamInfc M ζ hζ F hζF B β hβeq hβ hB
  | Sum.inr q => LamQc' M ζ hζ F B β hβeq hβ hB q.1

theorem LamV_inl (u : Unit) : LamV S M ζ hζ F hζF B β hβeq hβ hB (Sum.inl u) = LamInfc M ζ hζ F hζF B β hβeq hβ hB := rfl
theorem LamV_inr (q : ↥S) : LamV S M ζ hζ F hζF B β hβeq hβ hB (Sum.inr q) = LamQc' M ζ hζ F B β hβeq hβ hB q.1 := rfl

theorem LamV_surjective : ∀ v, Function.Surjective (LamV S M ζ hζ F hζF B β hβeq hβ hB v)
  | Sum.inl _ => LamInfc_surjective M ζ hζ F hζF B β hβeq hβ hB
  | Sum.inr q => LamQc'_surjective M ζ hζ F B β hβeq hβ hB q.1

theorem LamV_ker : ∀ (v : extArithIndex S) (s : Rep.res (Dv S F v).subtype (Rep.relationModuleInt B) ⟶ Yv S F v),
    LamV S M ζ hζ F hζF B β hβeq hβ hB v s = 0 ↔
      ∃ χ : Rep.res (Dv S F v).subtype (Rep.free ℤ (↥F ≃ₐ[ℚ] ↥F) B) ⟶ Yv S F v,
        s = (Rep.resFunctor (Dv S F v).subtype).map (Rep.relationModuleInt.ι B) ≫ χ
  | Sum.inl _, s => (LamInfc_ker M ζ hζ F hζF B β hβeq hβ hB s).trans ⟨fun ⟨χ, h⟩ => ⟨χ, h.symm⟩, fun ⟨χ, h⟩ => ⟨χ, h.symm⟩⟩
  | Sum.inr q, s => (LamQc'_ker M ζ hζ F B β hβeq hβ hB q.1 s).trans ⟨fun ⟨χ, h⟩ => ⟨χ, h.symm⟩, fun ⟨χ, h⟩ => ⟨χ, h.symm⟩⟩

noncomputable abbrev frobComp (s : Rep.relationModuleInt B ⟶ RepPi.obj (J0fam S F)) (v : extArithIndex S) :
    Rep.res (Dv S F v).subtype (Rep.relationModuleInt B) ⟶ Yv S F v :=
  ((Rep.resCoindAdjunction ℤ (Dv S F v).subtype).homEquiv (Rep.relationModuleInt B) (Yv S F v)).symm (s ≫ RepPi.proj (J0fam S F) v)

theorem frobComp_add (s s' : Rep.relationModuleInt B ⟶ RepPi.obj (J0fam S F)) (v : extArithIndex S) :
    frobComp S F B (s + s') v = frobComp S F B s v + frobComp S F B s' v := by
  simp only [frobComp, Preadditive.add_comp, Rep.coindFunctor_obj, Adjunction.mkOfHomEquiv_homEquiv]
  exact map_add (Rep.resCoindHomEquiv (Dv S F v).subtype (Rep.relationModuleInt B) (Yv S F v)).symm _ _

theorem frobComp_zero (v : extArithIndex S) : frobComp S F B 0 v = 0 := by
  simp only [frobComp, Limits.zero_comp, Rep.coindFunctor_obj, Adjunction.mkOfHomEquiv_homEquiv]
  exact map_zero (Rep.resCoindHomEquiv (Dv S F v).subtype (Rep.relationModuleInt B) (Yv S F v)).symm

noncomputable def LJ1 : (Rep.relationModuleInt B ⟶ NumberField.SArchIdele.obj ℚ ↥F (Sq S)) →+
    (∀ v : extArithIndex S, ↥(continuousH1 (extArithLoc S v) (Rep.res (extArithLoc S v) M))) where
  toFun s v := LamV S M ζ hζ F hζF B β hβeq hβ hB v (frobComp S F B (s ≫ rHom S F) v)
  map_zero' := by funext v; rw [Limits.zero_comp, frobComp_zero, map_zero]; rfl
  map_add' s s' := by funext v; rw [Preadditive.add_comp, frobComp_add, map_add]; rfl

theorem LJ1_apply (s : Rep.relationModuleInt B ⟶ NumberField.SArchIdele.obj ℚ ↥F (Sq S)) (v : extArithIndex S) :
    LJ1 S M ζ hζ F hζF B β hβeq hβ hB s v = LamV S M ζ hζ F hζF B β hβeq hβ hB v (frobComp S F B (s ≫ rHom S F) v) := rfl

def SHAPIRO_F := GroupCohomology.RepPi.forall_exists_comp_proj_and_iff_exists_eq_comp_of_coind (Dv S F) (Yv S F)
    (Rep.relationModuleInt.ι B) (fun v => ↥(continuousH1 (extArithLoc S v) (Rep.res (extArithLoc S v) M)))
    (LamV S M ζ hζ F hζF B β hβeq hβ hB) (LamV_surjective S M ζ hζ F hζF B β hβeq hβ hB) (LamV_ker S M ζ hζ F hζF B β hβeq hβ hB)

theorem LJ1_surjective : Function.Surjective (LJ1 S M ζ hζ F hζF B β hβeq hβ hB) := by
  intro t
  obtain ⟨s0, hs0⟩ := (SHAPIRO_F S M ζ hζ F hζF B β hβeq hβ hB).1 t
  refine ⟨s0 ≫ rInv S F, funext fun v => ?_⟩
  rw [LJ1_apply, Category.assoc, rInv_rHom, Category.comp_id]
  exact hs0 v

theorem LJ1_eq_zero_iff (s : Rep.relationModuleInt B ⟶ NumberField.SArchIdele.obj ℚ ↥F (Sq S)) :
    LJ1 S M ζ hζ F hζF B β hβeq hβ hB s = 0 ↔ ∃ χ : Rep.free ℤ (↥F ≃ₐ[ℚ] ↥F) B ⟶ NumberField.SArchIdele.obj ℚ ↥F (Sq S),
      s = Rep.relationModuleInt.ι B ≫ χ := by
  have h := (SHAPIRO_F S M ζ hζ F hζF B β hβeq hβ hB).2 (s ≫ rHom S F)
  constructor
  · intro h0
    obtain ⟨χ, hχ⟩ := h.1 (fun v => by have := congrFun h0 v; exact this)
    refine ⟨χ ≫ rInv S F, ?_⟩
    rw [← Category.assoc, ← hχ, Category.assoc, rHom_rInv, Category.comp_id]
  · rintro ⟨χ, rfl⟩
    funext v
    have := h.2 ⟨χ ≫ rHom S F, by rw [Category.assoc]⟩
    exact this v

end LJ1
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

end Reduce95
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

namespace Reduce95
open ExtCitation groupCohomology GroupCohomology M4aHerbrand

section alphaF

variable {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes)
  (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F]
  (hunr : ∀ w : HeightOneSpectrum (𝓞 ↥F), w ∉ TT S F → Ideal.ramificationIdx' (w.asIdeal.under (𝓞 ℚ)) w.asIdeal = 1)
  (B : Rep ℤ (↥F ≃ₐ[ℚ] ↥F)) [Fintype B] (hB : ∀ b : B, p • b = 0)

noncomputable abbrev CS : Rep ℤ (↥F ≃ₐ[ℚ] ↥F) := Rep.ofMulDistribMulAction (↥F ≃ₐ[ℚ] ↥F) (SIdeleClassGroup (𝓞 ↥F) ↥F (TT S F))

theorem hX' : (Rep.relationSeqInt B).ShortExact := Rep.relationSeqInt_shortExact B

def SCF4_F := M4aHerbrand.exists_fundamentalClass_sIdeleClassGroup ℚ ↥F (DD F) (TT S F) hunr (DD_stab S F) (hact_F F) (hactS_F S F)

noncomputable def uCF : groupCohomology (CS S F) 2 := (SCF4_F S F hunr).choose

def uCF_spec := (SCF4_F S F hunr).choose_spec

include hunr in

theorem hSURJ_F (θ : ↥(groupCohomology B 1) →+ ↥(groupCohomology (CS S F) 2)) :
    ∃ φ : Rep.relationModuleInt B ⟶ CS S F, ∀ y : ↥(groupCohomology B 1),
      (groupCohomology.map (MonoidHom.id _) φ 2).hom ((groupCohomology.δ (hX' F B) 1 2 rfl).hom y) = θ y :=
  Rep.exists_hom_relationModuleInt_forall_map_delta_eq (CS S F) (uCF S F hunr) (uCF_spec S F hunr).1
    (fun H _ => (uCF_spec S F hunr).2.1 H) (uCF_spec S F hunr).2.2 B (hX' F B) θ

end alphaF
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

end Reduce95
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

namespace Reduce95
open ExtCitation groupCohomology GroupCohomology M4aHerbrand

section hID
open scoped Classical

variable {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes)
  (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) [FiniteDimensional (ZMod p) M]
  (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p)
  (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F] [IsTotallyComplex ↥F]
  (hζF : ζ ∈ F)
  (hunr : ∀ w : HeightOneSpectrum (𝓞 ↥F), w ∉ TT S F → Ideal.ramificationIdx' (w.asIdeal.under (𝓞 ℚ)) w.asIdeal = 1)
  (B : Rep ℤ (↥F ≃ₐ[ℚ] ↥F)) [Fintype B] (β : B →+ M.dualTwist (cycloChar p))
  (hβeq : ∀ (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (b : B),
    β (B.ρ (AlgEquiv.restrictNormalHom ↥F γ) b) = (M.dualTwist (cycloChar p)).ρ γ (β b))
  (hβ : Function.Bijective β) (hB : ∀ b : B, p • b = 0)

theorem hXv' (v : extArithIndex S) : ((Rep.relationSeqInt B).map (Rep.resFunctor (Dv S F v).subtype)).ShortExact :=
  (hX' F B).map_of_exact (Rep.resFunctor (Dv S F v).subtype)

variable
  (θ : ∀ v : extArithIndex S,
    continuousH1 (extArithLoc S v) (Rep.res (extArithLoc S v) M) →ₗ[ZMod p]
      Module.Dual (ZMod p) (continuousH1 (extArithLoc S v) (Rep.res (extArithLoc S v) (M.dualTwist (cycloChar p)))))
  (hloc : ∀ y ∈ continuousH1S S (M.dualTwist (cycloChar p)), ∀ v : extArithIndex S,
    locTotal (extArithLoc S) (M.dualTwist (cycloChar p)) y v ∈ continuousH1 (extArithLoc S v) (Rep.res (extArithLoc S v) (M.dualTwist (cycloChar p))))
  (infl : ↥(groupCohomology B 1) →+ H1 (M.dualTwist (cycloChar p)))
  (u : extArithIndex S → (ZMod p)ˣ)

end hID
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

end Reduce95
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

namespace Reduce95
open ExtCitation

section hunr

variable (S : Finset Nat.Primes) (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F]

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

theorem asIdeal_eq_span_primesEquiv (v : HeightOneSpectrum (𝓞 ℚ)) :
    v.asIdeal = Ideal.span {((Rat.HeightOneSpectrum.primesEquiv v : ℕ) : 𝓞 ℚ)} := by
  have h := Rat.HeightOneSpectrum.span_natGenerator (R := 𝓞 ℚ) v
  have h2 : v.asIdeal = (v.asIdeal.map (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ))).map (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).symm := by
    rw [Ideal.map_symm, Ideal.comap_map_of_bijective _ (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).bijective]
  rw [h2, ← h, Ideal.map_span, Set.image_singleton, map_natCast]
  rfl

theorem hunr_F (hFS : F.IsUnramifiedOutside S) (w : HeightOneSpectrum (𝓞 ↥F)) (hw : w ∉ TT S F) :
    Ideal.ramificationIdx' (w.asIdeal.under (𝓞 ℚ)) w.asIdeal = 1 := by
  set v : HeightOneSpectrum (𝓞 ℚ) := w.under (𝓞 ℚ) with hvdef
  set ℓ : Nat.Primes := Rat.HeightOneSpectrum.primesEquiv v with hℓdef
  have hℓv : ((ℓ : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := (natCast_mem_asIdeal_iff v ℓ).2 rfl
  have hℓw : ((ℓ : ℕ) : 𝓞 ↥F) ∈ w.asIdeal := by
    have : algebraMap (𝓞 ℚ) (𝓞 ↥F) (((ℓ : ℕ) : 𝓞 ℚ)) ∈ w.asIdeal := hℓv
    rwa [map_natCast] at this
  have hℓS : ℓ ∉ S := fun h => hw ((NumberField.mem_placesOverPrimes_iff _ _ _).2 ⟨ℓ, h, hℓw⟩)
  have hHin : ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime (ℓ : ℕ) → P.inertiaSubgroupIn ℚ ≤ F.fixingSubgroup :=
    fun P hP => hFS.2 ℓ hℓS P hP
  have h1 := NumberField.ramificationIdx_span_eq_one_of_forall_liesOverPrime_inertiaSubgroupIn_le_fixingSubgroup F (ℓ : ℕ) ℓ.2 hHin
    w.asIdeal w.isMaximal hℓw
  have hmapZ : (Ideal.span {(((ℓ : ℕ) : ℕ) : ℤ)}).map (algebraMap ℤ (𝓞 ↥F)) = Ideal.span {((ℓ : ℕ) : 𝓞 ↥F)} := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  have hmapQ : (w.asIdeal.under (𝓞 ℚ)).map (algebraMap (𝓞 ℚ) (𝓞 ↥F)) = Ideal.span {((ℓ : ℕ) : 𝓞 ↥F)} := by
    have hv : w.asIdeal.under (𝓞 ℚ) = v.asIdeal := rfl
    rw [hv, asIdeal_eq_span_primesEquiv v, Ideal.map_span, Set.image_singleton, map_natCast]
  unfold Ideal.ramificationIdx' at h1 ⊢
  rw [hmapQ, ← hmapZ]
  exact h1

end hunr
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

end Reduce95
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

namespace Reduce95

section totallyComplex

variable {p : ℕ} [Fact p.Prime] (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p)
  (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F]

include hζ in
theorem isTotallyComplex_of_mem (hp2 : p ≠ 2) (hζF : ζ ∈ F) : IsTotallyComplex ↥F := by
  refine ⟨fun v => ?_⟩
  rw [NumberField.InfinitePlace.isComplex_iff, NumberField.ComplexEmbedding.isReal_iff]
  intro hreal

  set φ := v.embedding with hφ
  have hz : IsPrimitiveRoot (⟨ζ, hζF⟩ : ↥F) p :=
    hζ.of_map_of_injective (f := algebraMap ↥F (AlgebraicClosure ℚ)) (algebraMap ↥F (AlgebraicClosure ℚ)).injective
  have hφz : IsPrimitiveRoot (φ ⟨ζ, hζF⟩) p := hz.map_of_injective φ.injective

  have hconj : starRingEnd ℂ (φ ⟨ζ, hζF⟩) = φ ⟨ζ, hζF⟩ := by
    have := RingHom.congr_fun hreal ⟨ζ, hζF⟩
    simpa [NumberField.ComplexEmbedding.conjugate] using this

  have hnorm : ‖φ ⟨ζ, hζF⟩‖ = 1 := hφz.norm'_eq_one (Fact.out : p.Prime).ne_zero
  have hre : ((φ ⟨ζ, hζF⟩).re : ℂ) = φ ⟨ζ, hζF⟩ := (Complex.conj_eq_iff_re.mp hconj)
  have hsq : (φ ⟨ζ, hζF⟩) ^ 2 = 1 := by
    rw [← hre, ← Complex.ofReal_pow, sq]
    have habs : |(φ ⟨ζ, hζF⟩).re| = 1 := by
      have := Complex.abs_re_le_norm (φ ⟨ζ, hζF⟩)
      rw [← hre, Complex.norm_real, Real.norm_eq_abs] at hnorm
      exact hnorm
    rcases abs_eq_abs.mp (habs.trans (abs_one).symm) with h | h
    · rw [h, mul_one, Complex.ofReal_one]
    · rw [h, neg_mul_neg, mul_one, Complex.ofReal_one]
  have hdvd : p ∣ 2 := hφz.dvd_of_pow_eq_one 2 hsq
  have : p = 2 := (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp hdvd
  exact hp2 this

end totallyComplex
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

end Reduce95
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

set_option autoImplicit false
open CategoryTheory groupCohomology IsDedekindDomain NumberField

namespace Reduce95
open ExtCitation M4aHerbrand
open scoped NumberField.PlaceDecomp

local instance factPrimesE2 (q : Nat.Primes) : Fact ((q : ℕ)).Prime := ⟨q.2⟩

section hXv
variable {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
  (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F]
  (B : Rep ℤ (↥F ≃ₐ[ℚ] ↥F)) (β : B →+ M.dualTwist (cycloChar p))
  (hβeq : ∀ (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (b : B),
    β (B.ρ (AlgEquiv.restrictNormalHom ↥F γ) b) = (M.dualTwist (cycloChar p)).ρ γ (β b))

theorem hXvB (v : extArithIndex S) :
    ((Rep.relationSeqInt B).map (Rep.resFunctor (Dv S F v).subtype)).ShortExact :=
  (Rep.relationSeqInt_shortExact B).map_of_exact (Rep.resFunctor (Dv S F v).subtype)

include hβeq in

noncomputable def inflC' (n : cocycles₁ B) : cocycles₁ (M.dualTwist (cycloChar p)) :=
  ⟨fun γ => β (n (AlgEquiv.restrictNormalHom ↥F γ)), (mem_cocycles₁_iff _).2 fun g h => by
    have hn := (mem_cocycles₁_iff (⇑n)).1 n.2 (AlgEquiv.restrictNormalHom ↥F g) (AlgEquiv.restrictNormalHom ↥F h)
    rw [map_mul, hn, map_add, hβeq]⟩

@[scoped simp] theorem inflC'_apply (n : cocycles₁ B) (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    inflC' M F B β hβeq n γ = β (n (AlgEquiv.restrictNormalHom ↥F γ)) := rfl

end hXv
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

section uQ
variable {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (q : ↥S) (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p)

noncomputable def uQ : (ZMod p)ˣ :=
  (NumberField.PlaceDecomp.exists_unit_inv_map_delta_res_eq_theta_localBridge S q ζ hζ).choose

def uQ_spec := (NumberField.PlaceDecomp.exists_unit_inv_map_delta_res_eq_theta_localBridge S q ζ hζ).choose_spec

end uQ
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

section hLOCfin
variable {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
  [FiniteDimensional (ZMod p) M] (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p)
  (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F]
  (B : Rep ℤ (↥F ≃ₐ[ℚ] ↥F)) [Fintype B] (β : B →+ M.dualTwist (cycloChar p))
  (hβeq : ∀ (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (b : B),
    β (B.ρ (AlgEquiv.restrictNormalHom ↥F γ) b) = (M.dualTwist (cycloChar p)).ρ γ (β b))
  (hβ : Function.Bijective β) (hB : ∀ b : B, p • b = 0)
  (hunr : ∀ w : HeightOneSpectrum (𝓞 ↥F), w ∉ TT S F → Ideal.ramificationIdx' (w.asIdeal.under (𝓞 ℚ)) w.asIdeal = 1)

theorem lamV_inr_eq_F (q : ↥S) :
    lamV S F (LF S F) (Sum.inr q) =
      lamWF F (wq F q.1) ≫ (Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F (wq F q.1)).subtype).map (qSF S F) := by
  unfold LF
  exact lamV_inr_eq S F (DD F) (TT S F) (hactI_F F) (hact_F F) (hactS_F S F) (PhiF S F) (PhiF_eq S F) (PhiF_S S F) (PhiF_out S F)
    (PhiF_inf S F) (NumberField.PlaceTransport.stabilizer_eq_decomp ℚ ↥F) (iotaDF F) (iotaDF_spec F) q

end hLOCfin
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

section hLOCinf
variable {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
  [FiniteDimensional (ZMod p) M]
  (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F]
  (B : Rep ℤ (↥F ≃ₐ[ℚ] ↥F)) (hB : ∀ b : B, p • b = 0)
  (hunr : ∀ w : HeightOneSpectrum (𝓞 ↥F), w ∉ TT S F → Ideal.ramificationIdx' (w.asIdeal.under (𝓞 ℚ)) w.asIdeal = 1)

lemma zsmul_hom4_eq_zero_e2 {M₀ M₁ M₂ M₃ M₄ : ModuleCat.{0} ℤ} (f₁ : M₀ ⟶ M₁) (f₂ : M₁ ⟶ M₂) (f₃ : M₂ ⟶ M₃) (f₄ : M₃ ⟶ M₄)
    (n : M₀) (c : ℤ) (hn : c • n = 0) : c • f₄.hom (f₃.hom (f₂.hom (f₁.hom n))) = 0 := by
  rw [← map_zsmul f₄.hom, ← map_zsmul f₃.hom, ← map_zsmul f₂.hom, ← map_zsmul f₁.hom, hn, map_zero, map_zero, map_zero, map_zero]

lemma module_zsmul_eq {A : Type*} [AddCommGroup A] [inst : Module ℤ A] (c : ℤ) (a : A) :
    @HSMul.hSMul ℤ A A (@instHSMul ℤ A inst.toSMul) c a = @HSMul.hSMul ℤ A A (@instHSMul ℤ A ZSMul.toSMul) c a :=
  int_smul_eq_zsmul inst c a

lemma eq_zero_of_zsmul_of_isCoprime {A : Type*} [AddCommGroup A] {a b : ℤ} (h : IsCoprime a b) (z : A)
    (ha : a • z = 0) (hb : b • z = 0) : z = 0 := by
  obtain ⟨s, t, hst⟩ := h
  rw [← one_smul ℤ z, ← hst, add_smul, mul_smul, mul_smul, ha, hb, smul_zero, smul_zero, add_zero]

end hLOCinf
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

end Reduce95
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

namespace Reduce95
open ExtCitation groupCohomology GroupCohomology M4aHerbrand

section hLOCall
open scoped Classical

variable {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes)
  (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) [FiniteDimensional (ZMod p) M]
  (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p)
  (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F] [IsTotallyComplex ↥F]
  (hζF : ζ ∈ F)
  (hunr : ∀ w : HeightOneSpectrum (𝓞 ↥F), w ∉ TT S F → Ideal.ramificationIdx' (w.asIdeal.under (𝓞 ℚ)) w.asIdeal = 1)
  (B : Rep ℤ (↥F ≃ₐ[ℚ] ↥F)) [Fintype B] (β : B →+ M.dualTwist (cycloChar p))
  (hβeq : ∀ (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (b : B),
    β (B.ρ (AlgEquiv.restrictNormalHom ↥F γ) b) = (M.dualTwist (cycloChar p)).ρ γ (β b))
  (hβ : Function.Bijective β) (hB : ∀ b : B, p • b = 0)
  (hp2 : p ≠ 2)

local instance factPrimesL (q : Nat.Primes) : Fact ((q : ℕ)).Prime := ⟨q.2⟩

noncomputable def uV : extArithIndex S → (ZMod p)ˣ
  | Sum.inl _ => 1
  | Sum.inr q => uQ S q ζ hζ

variable
  (θ : ∀ v : extArithIndex S,
    continuousH1 (extArithLoc S v) (Rep.res (extArithLoc S v) M) →ₗ[ZMod p]
      Module.Dual (ZMod p) (continuousH1 (extArithLoc S v) (Rep.res (extArithLoc S v) (M.dualTwist (cycloChar p)))))
  (hθ : ∀ q : ↥S, IsTheta1 (extArithLoc S (Sum.inr q))
        (Module.Dual.eval (ZMod p) M :
          Rep.res (extArithLoc S (Sum.inr q)) M →ₗ[ZMod p]
            Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p)) →ₗ[ZMod p]
              ofChar (k := ZMod p) ((cycloChar p).comp (extArithLoc S (Sum.inr q))))
        (localInv p ζ (q : Nat.Primes)) (θ (Sum.inr q)))
  (hloc : ∀ y ∈ continuousH1S S (M.dualTwist (cycloChar p)), ∀ v : extArithIndex S,
    locTotal (extArithLoc S) (M.dualTwist (cycloChar p)) y v ∈ continuousH1 (extArithLoc S v) (Rep.res (extArithLoc S v) (M.dualTwist (cycloChar p))))
  (infl : ↥(groupCohomology B 1) →+ H1 (M.dualTwist (cycloChar p)))
  (hinflpin : ∀ (n : cocycles₁ B) (ny : cocycles₁ (M.dualTwist (cycloChar p))),
      (∀ γ, ny γ = β (n (AlgEquiv.restrictNormalHom ↥F γ))) →
        infl ((H1π B).hom n) = (H1π (M.dualTwist (cycloChar p))).hom ny)

end hLOCall
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

end Reduce95
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

set_option autoImplicit false
open CategoryTheory IsDedekindDomain NumberField

namespace Reduce95
open ExtCitation groupCohomology
open scoped NumberField.PlaceDecomp

section K1generic

def linOfAdd {V W : Type} [AddCommGroup V] [AddCommGroup W] [Module ℤ V] [Module ℤ W] (ψ : V →+ W) : V →ₗ[ℤ] W where
  toFun := ψ
  map_add' := ψ.map_add
  map_smul' c x := map_intCast_smul ψ ℤ ℤ c x

@[scoped simp] theorem linOfAdd_apply {V W : Type} [AddCommGroup V] [AddCommGroup W] [Module ℤ V] [Module ℤ W] (ψ : V →+ W) (x : V) :
    linOfAdd ψ x = ψ x := rfl

theorem finite_of_iso_free {D : Type} [Group D] {β : Type} {P : Rep ℤ D} [Module.Finite ℤ P]
    (e : P ≅ Rep.free ℤ D β) : Finite β := by
  haveI : Module.Finite ℤ (Rep.free ℤ D β) := Module.Finite.equiv (Representation.equivOfIso e).toLinearEquiv
  have b := Finsupp.basis (R := ℤ) (ι := β) (fun _ => (MonoidAlgebra.basis D ℤ : Module.Basis D ℤ (MonoidAlgebra ℤ D)))
  haveI : Module.Finite ℤ (β →₀ MonoidAlgebra ℤ D) := by exact (inferInstance : Module.Finite ℤ (Rep.free ℤ D β))
  haveI := Module.Finite.finite_basis b
  exact Finite.of_injective (fun x : β => (⟨x, 1⟩ : Σ _ : β, D)) (fun _ _ h => congrArg Sigma.fst h)

section ihomTransport

variable {D H : Type} [Group D] [Group H] (π : H →* D) {P P' : Rep ℤ D} (e : P ≅ P') (A : Rep ℤ H)

noncomputable def preHom : ((ihom (Rep.res π P')).obj A) →+ ((ihom (Rep.res π P)).obj A) where
  toFun χ := (show P'.V →ₗ[ℤ] A.V from χ) ∘ₗ e.hom.hom.toLinearMap
  map_zero' := LinearMap.zero_comp _
  map_add' _ _ := LinearMap.add_comp _ _ _

noncomputable def preInv : ((ihom (Rep.res π P)).obj A) →+ ((ihom (Rep.res π P')).obj A) where
  toFun χ := (show P.V →ₗ[ℤ] A.V from χ) ∘ₗ e.inv.hom.toLinearMap
  map_zero' := LinearMap.zero_comp _
  map_add' _ _ := LinearMap.add_comp _ _ _

theorem preHom_apply (χ : (ihom (Rep.res π P')).obj A) (x : P) :
    LinearMap.toAddMonoidHom (preHom π e A χ) x = LinearMap.toAddMonoidHom χ (e.hom.hom x) := rfl

theorem preInv_apply (χ : (ihom (Rep.res π P)).obj A) (x : P') :
    LinearMap.toAddMonoidHom (preInv π e A χ) x = LinearMap.toAddMonoidHom χ (e.inv.hom x) := rfl

theorem preHom_preInv (χ : (ihom (Rep.res π P)).obj A) : preHom π e A (preInv π e A χ) = χ :=
  LinearMap.ext fun x => congrArg (show P.V →ₗ[ℤ] A.V from χ) (Rep.inv_hom_apply _ _ e x)

theorem preHom_ρ (h : H) (χ : (ihom (Rep.res π P')).obj A) :
    preHom π e A (((ihom (Rep.res π P')).obj A).ρ h χ) = ((ihom (Rep.res π P)).obj A).ρ h (preHom π e A χ) := by
  apply LinearMap.ext
  intro x
  change A.ρ h ((show P'.V →ₗ[ℤ] A.V from χ) (P'.ρ (π h⁻¹) (e.hom.hom x))) =
    A.ρ h ((show P'.V →ₗ[ℤ] A.V from χ) (e.hom.hom (P.ρ (π h⁻¹) x)))
  exact congrArg (fun y => A.ρ h ((show P'.V →ₗ[ℤ] A.V from χ) y)) (Rep.hom_comm_apply e.hom (π h⁻¹) x).symm

theorem preInv_ρ (h : H) (χ : (ihom (Rep.res π P)).obj A) :
    preInv π e A (((ihom (Rep.res π P)).obj A).ρ h χ) = ((ihom (Rep.res π P')).obj A).ρ h (preInv π e A χ) := by
  apply LinearMap.ext
  intro x
  change A.ρ h ((show P.V →ₗ[ℤ] A.V from χ) (P.ρ (π h⁻¹) (e.inv.hom x))) =
    A.ρ h ((show P.V →ₗ[ℤ] A.V from χ) (e.inv.hom (P'.ρ (π h⁻¹) x)))
  exact congrArg (fun y => A.ρ h ((show P.V →ₗ[ℤ] A.V from χ) y)) (Rep.hom_comm_apply e.inv (π h⁻¹) x).symm

noncomputable def preInvCocycle (u : cocycles₁ ((ihom (Rep.res π P)).obj A)) : cocycles₁ ((ihom (Rep.res π P')).obj A) :=
  ⟨fun h => preInv π e A (u h), (mem_cocycles₁_iff _).2 fun g h => by
    have hu := (mem_cocycles₁_iff (u : H → (ihom (Rep.res π P)).obj A)).1 u.2 g h
    change preInv π e A (u (g * h)) = _
    rw [hu, map_add, preInv_ρ]⟩

theorem preInvCocycle_apply (u : cocycles₁ ((ihom (Rep.res π P)).obj A)) (h : H) :
    (preInvCocycle π e A u : H → _) h = preInv π e A (u h) := rfl

end ihomTransport
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

end K1generic
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

section LamQ2

variable {p : ℕ} [Fact p.Prime] (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) [FiniteDimensional (ZMod p) M]
  (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p)
  (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F]
  (B : Rep ℤ (↥F ≃ₐ[ℚ] ↥F)) [Fintype B] (β : B →+ M.dualTwist (cycloChar p))
  (hβeq : ∀ (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (b : B),
    β (B.ρ (AlgEquiv.restrictNormalHom ↥F γ) b) = (M.dualTwist (cycloChar p)).ρ γ (β b))
  (hβ : Function.Bijective β) (hB : ∀ b : B, p • b = 0)
  (q : Nat.Primes)

local instance factPrimesK1 (q : Nat.Primes) : Fact ((q : ℕ)).Prime := ⟨q.2⟩

include hβeq hβ hB in
set_option maxHeartbeats 16000000 in
theorem exists_LamQ2 :
    ∃ Λ : H1 ((ihom (Rep.res (DQ F q).subtype (Rep.relationModuleInt B))).obj (XQ F q)) →+
        continuousH2 (primeLocalToGlobal q) (Rep.res (primeLocalToGlobal q) M),
      IsLocalBridge₂ (primeLocalToGlobal q) (piQ F q)
        ((Rep.resFunctor (DQ F q).subtype).map (Rep.relationModuleInt.ι B))
        ((Rep.resFunctor (DQ F q).subtype).map (Rep.freeCover B))
        (X := XQ F q)
        (A := (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)))
        (Units.map (PhiQ F q : (wq F q).adicCompletion ↥F →* PadicAlgCl q)).toAdditive
        (M := Rep.res (primeLocalToGlobal q) M)
        (kappaQF M F q B (kappa M ζ hζ B β)) Λ ∧
      Function.Injective Λ := by
  obtain ⟨hKR, hFIX, hH90⟩ := NumberField.PlaceDecomp.localBridge_hypotheses_padicAlgCl (q : ℕ) F (wq F q) (sigmaQ F q) (PhiQ F q)
    (hPhiF_q F q) (PhiQ_spec F q).2.1 (PhiQ_spec F q).2.2.1 (PhiQ_spec F q).2.2.2.1 (hcont_q F q)
  have hπlev : ∃ F' : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F' ∧
      ∀ s : primeLocalGaloisGroup q, primeLocalToGlobal q s ∈ F'.fixingSubgroup → piQ F q s = 1 := by
    have hrNH : ∀ g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, g ∈ F.fixingSubgroup → AlgEquiv.restrictNormalHom ↥F g = 1 := by
      intro g hg
      ext x
      change algebraMap ↥F (AlgebraicClosure ℚ) (AlgEquiv.restrictNormalHom ↥F g x) = ((1 : ↥F ≃ₐ[ℚ] ↥F) x : AlgebraicClosure ℚ)
      rw [AlgEquiv.one_apply]
      exact (AlgEquiv.restrictNormal_commutes g ↥F x).trans ((IntermediateField.mem_fixingSubgroup_iff _ _).1 hg x.1 x.2)
    refine ⟨F, inferInstance, fun s hs => Subtype.ext ?_⟩
    change AlgEquiv.restrictNormalHom ↥F ((sigmaQ F q)⁻¹ * primeLocalToGlobal q s * sigmaQ F q) = 1
    rw [map_mul, map_mul, hrNH _ hs, mul_one, ← map_mul, inv_mul_cancel, map_one]
  have hι : Function.Injective ((Units.map (PhiQ F q : (wq F q).adicCompletion ↥F →* PadicAlgCl q)).toAdditive) := by
    intro a b h
    have h' : Units.map (PhiQ F q : (wq F q).adicCompletion ↥F →* PadicAlgCl q) (Additive.toMul a) =
        Units.map (PhiQ F q : (wq F q).adicCompletion ↥F →* PadicAlgCl q) (Additive.toMul b) := congrArg Additive.toMul h
    have h'' : PhiQ F q ((Additive.toMul a : ((wq F q).adicCompletion ↥F)ˣ) : (wq F q).adicCompletion ↥F) =
        PhiQ F q ((Additive.toMul b : ((wq F q).adicCompletion ↥F)ˣ) : (wq F q).adicCompletion ↥F) :=
      congrArg Units.val h'
    exact congrArg Additive.ofMul (Units.ext ((PhiQ F q).injective h''))
  have hιeq : ∀ (h : primeLocalGaloisGroup q) (x : XQ F q),
      (Units.map (PhiQ F q : (wq F q).adicCompletion ↥F →* PadicAlgCl q)).toAdditive ((XQ F q).ρ (piQ F q h) x) =
        (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)).ρ h
          ((Units.map (PhiQ F q : (wq F q).adicCompletion ↥F →* PadicAlgCl q)).toAdditive x) := by
    intro τ x
    obtain ⟨u, rfl⟩ : ∃ v : ((wq F q).adicCompletion ↥F)ˣ, Additive.ofMul v = x := ⟨Additive.toMul x, rfl⟩
    change (Units.map (PhiQ F q : (wq F q).adicCompletion ↥F →* PadicAlgCl q)).toAdditive
        ((Rep.ofMulDistribMulAction ↥(DQ F q) ((wq F q).adicCompletion ↥F)ˣ).ρ (piQ F q τ) (Additive.ofMul u)) =
      (Rep.ofMulDistribMulAction (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q) (PadicAlgCl q)ˣ).ρ
        (show PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q from τ)
        (Additive.ofMul (Units.map (PhiQ F q : (wq F q).adicCompletion ↥F →* PadicAlgCl q) u))
    rw [Rep.ofMulDistribMulAction_ρ_apply_apply, Rep.ofMulDistribMulAction_ρ_apply_apply]
    apply congrArg Additive.ofMul
    apply Units.ext
    change PhiQ F q (((piQ F q τ • u : ((wq F q).adicCompletion ↥F)ˣ)) : (wq F q).adicCompletion ↥F) =
      (show PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q from τ) (PhiQ F q (u : (wq F q).adicCompletion ↥F))
    rw [NumberField.PlaceDecomp.coe_smul_units]
    exact heqv_q F q τ u
  have hκeq := kappaQF_eqv M F q B (kappa M ζ hζ B β) (kappa_equivariant M ζ hζ (AlgEquiv.restrictNormalHom ↥F) B β hβeq)
  have hκ := kappaQ_perfect M ζ hζ (q : ℕ) (sigmaQ F q) B (kappa M ζ hζ B β) hB (kappa_perfect M ζ hζ B β hβ hB)
  have hdiv : ∀ φ : Rep.res (DQ F q).subtype (Rep.relationModuleInt B) →+ XQ F q,
      ∃ ψ : (ihom (Rep.res (piQ F q) (Rep.res (DQ F q).subtype (Rep.free ℤ (↥F ≃ₐ[ℚ] ↥F) B)))).obj
          (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)),
        (∀ x : Rep.res (DQ F q).subtype (Rep.relationModuleInt B),
          LinearMap.toAddMonoidHom ψ (((Rep.resFunctor (DQ F q).subtype).map (Rep.relationModuleInt.ι B)).hom x) =
            (Units.map (PhiQ F q : (wq F q).adicCompletion ↥F →* PadicAlgCl q)).toAdditive (φ x)) ∧
        ∃ F' : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F' ∧
          ∀ s : primeLocalGaloisGroup q, primeLocalToGlobal q s ∈ F'.fixingSubgroup →
            ∀ x : Rep.res (DQ F q).subtype (Rep.free ℤ (↥F ≃ₐ[ℚ] ↥F) B),
              (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)).ρ s (LinearMap.toAddMonoidHom ψ x) =
                LinearMap.toAddMonoidHom ψ x := by
    intro φ
    have hfreeW : @Module.Free ℤ (B →₀ MonoidAlgebra ℤ (↥F ≃ₐ[ℚ] ↥F)) _ _ (AddCommGroup.toIntModule _) := by
      convert (inferInstance : Module.Free ℤ (B →₀ MonoidAlgebra ℤ (↥F ≃ₐ[ℚ] ↥F)))
    have hfinW : @Module.Finite ℤ (B →₀ MonoidAlgebra ℤ (↥F ≃ₐ[ℚ] ↥F)) _ _ (AddCommGroup.toIntModule _) := by
      haveI : Finite (↥F ≃ₐ[ℚ] ↥F) := inferInstance
      haveI : Module.Finite ℤ (MonoidAlgebra ℤ (↥F ≃ₐ[ℚ] ↥F)) := Module.Finite.of_basis (MonoidAlgebra.basis (↥F ≃ₐ[ℚ] ↥F) ℤ)
      convert (Module.Finite.finsupp : Module.Finite ℤ (B →₀ MonoidAlgebra ℤ (↥F ≃ₐ[ℚ] ↥F)))
    obtain ⟨ψ, hψ1, F₂, hF₂, hψ2⟩ := @hKR (Rep.relationCarrier B) (B →₀ MonoidAlgebra ℤ (↥F ≃ₐ[ℚ] ↥F)) _ _ hfreeW hfinW
      (Rep.relationModuleInt.ι B).hom.toLinearMap.toAddMonoidHom.toIntLinearMap
      (fun a b h => relationModuleInt_ι_injective B h) φ.toIntLinearMap
    exact ⟨linOfAdd ψ.toAddMonoidHom, fun x => hψ1 x, F₂, hF₂, fun s hs x => hψ2 s hs x⟩
  obtain ⟨Λ, hΛ⟩ := groupCohomology.exists_isLocalBridge2 (primeLocalToGlobal q) (piQ F q) hπlev
    ((Rep.resFunctor (DQ F q).subtype).map (Rep.relationModuleInt.ι B)) ((Rep.resFunctor (DQ F q).subtype).map (Rep.freeCover B))
    (exact_ι_freeCover B) (freeCover_surjective B)
    (X := XQ F q) (A := (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)))
    ((Units.map (PhiQ F q : (wq F q).adicCompletion ↥F →* PadicAlgCl q)).toAdditive) hι hιeq
    (M := Rep.res (primeLocalToGlobal q) M) (kappaQF M F q B (kappa M ζ hζ B β)) hκeq hκ hdiv
  refine ⟨Λ, hΛ, ?_⟩
  have hιfix : ∀ a : (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)),
      (∀ s : primeLocalGaloisGroup q, piQ F q s = 1 →
        (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)).ρ s a = a) →
      ∃ x : XQ F q, (Units.map (PhiQ F q : (wq F q).adicCompletion ↥F →* PadicAlgCl q)).toAdditive x = a := by
    intro a ha
    obtain ⟨x, hx⟩ := hFIX (Additive.toMul a) (fun τ hτ => by
      have h1 : piQ F q τ = 1 := Subtype.ext hτ
      have h2 := ha τ h1
      change (Rep.ofMulDistribMulAction (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q) (PadicAlgCl q)ˣ).ρ
          (show PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q from τ) (Additive.ofMul (Additive.toMul a)) = Additive.ofMul (Additive.toMul a) at h2
      rw [Rep.ofMulDistribMulAction_ρ_apply_apply] at h2
      exact congrArg Units.val (Additive.ofMul.injective h2))
    refine ⟨Additive.ofMul x, ?_⟩
    change Additive.ofMul (Units.map (PhiQ F q : (wq F q).adicCompletion ↥F →* PadicAlgCl q) x) = a
    rw [show Units.map (PhiQ F q : (wq F q).adicCompletion ↥F →* PadicAlgCl q) x = Additive.toMul a from Units.ext hx]
    rfl
  have h90 : ∀ u : cocycles₁ ((ihom (Rep.res (piQ F q) (Rep.res (DQ F q).subtype (Rep.free ℤ (↥F ≃ₐ[ℚ] ↥F) B)))).obj
          (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q))),
      IsLevelConstant₁ (primeLocalToGlobal q) (u : primeLocalGaloisGroup q → _) →
      ∃ χ : (ihom (Rep.res (piQ F q) (Rep.res (DQ F q).subtype (Rep.free ℤ (↥F ≃ₐ[ℚ] ↥F) B)))).obj
          (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)),
        (∃ F' : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F' ∧
          ∀ s : primeLocalGaloisGroup q, primeLocalToGlobal q s ∈ F'.fixingSubgroup →
            ∀ x : Rep.res (DQ F q).subtype (Rep.free ℤ (↥F ≃ₐ[ℚ] ↥F) B),
              (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)).ρ s (LinearMap.toAddMonoidHom χ x) =
                LinearMap.toAddMonoidHom χ x) ∧
        (d₀₁ _).hom χ = (u : primeLocalGaloisGroup q → _) := by
    intro u hu
    obtain ⟨βT, ⟨e⟩⟩ := Rep.nonempty_res_free_iso_free (k := ℤ) (DQ F q) (B : Type)
    haveI : Finite (↥F ≃ₐ[ℚ] ↥F) := inferInstance
    haveI : Module.Finite ℤ (MonoidAlgebra ℤ (↥F ≃ₐ[ℚ] ↥F)) := Module.Finite.of_basis (MonoidAlgebra.basis (↥F ≃ₐ[ℚ] ↥F) ℤ)
    haveI : Module.Finite ℤ (Rep.res (DQ F q).subtype (Rep.free ℤ (↥F ≃ₐ[ℚ] ↥F) B)) :=
      by exact (Module.Finite.finsupp : Module.Finite ℤ (B →₀ MonoidAlgebra ℤ (↥F ≃ₐ[ℚ] ↥F)))
    haveI : Finite βT := finite_of_iso_free e

    let A' : Rep ℤ (primeLocalGaloisGroup q) := (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q))
    let u' := preInvCocycle (piQ F q) e A' u
    have hu' : IsLevelConstant₁ (primeLocalToGlobal q) (u' : primeLocalGaloisGroup q → _) := by
      obtain ⟨F₁, hF₁, h⟩ := hu
      exact ⟨F₁, hF₁, fun g s hs => by
        change preInv (piQ F q) e A' (u (g * s)) = preInv (piQ F q) e A' (u g)
        rw [h g s hs]⟩
    obtain ⟨χ', ⟨F₂, hF₂, hfix⟩, hd⟩ := hH90 βT (piQ F q) (hpi_q F q) u' hu'
    refine ⟨preHom (piQ F q) e A' χ', ⟨F₂, hF₂, fun s hs x => hfix s hs (e.hom.hom x)⟩, ?_⟩
    funext h
    have hdh := congrFun hd h
    rw [d₀₁_hom_apply] at hdh ⊢
    change _ = preInv (piQ F q) e A' (u h) at hdh
    calc _ = preHom (piQ F q) e A' (((ihom (Rep.res (piQ F q) (Rep.free ℤ ↥(DQ F q) βT))).obj A').ρ h χ') - preHom (piQ F q) e A' χ' :=
          congrArg (fun t => t - preHom (piQ F q) e A' χ') (preHom_ρ (piQ F q) e A' h χ').symm
      _ = preHom (piQ F q) e A' (preInv (piQ F q) e A' (u h)) := by
          rw [← map_sub]; exact congrArg (preHom (piQ F q) e A') hdh
      _ = u h := preHom_preInv (piQ F q) e A' (u h)
  exact groupCohomology.isLocalBridge2_injective (primeLocalToGlobal q) (piQ F q) (hpisurj_q F q) hπlev
    ((Rep.resFunctor (DQ F q).subtype).map (Rep.relationModuleInt.ι B)) ((Rep.resFunctor (DQ F q).subtype).map (Rep.freeCover B))
    (relationModuleInt_ι_injective B) (exact_ι_freeCover B) (freeCover_surjective B)
    (X := XQ F q) (A := (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)))
    ((Units.map (PhiQ F q : (wq F q).adicCompletion ↥F →* PadicAlgCl q)).toAdditive) hι hιeq hιfix
    (M := Rep.res (primeLocalToGlobal q) M) (kappaQF M F q B (kappa M ζ hζ B β)) hκeq hκ hdiv h90 hΛ

noncomputable def LamQ2 : H1 ((ihom (Rep.res (DQ F q).subtype (Rep.relationModuleInt B))).obj (XQ F q)) →+
    continuousH2 (primeLocalToGlobal q) (Rep.res (primeLocalToGlobal q) M) :=
  (exists_LamQ2 M ζ hζ F B β hβeq hβ hB q).choose

def LamQ2_spec := (exists_LamQ2 M ζ hζ F B β hβeq hβ hB q).choose_spec

def LamQ2_bridge := (LamQ2_spec M ζ hζ F B β hβeq hβ hB q).1

theorem LamQ2_injective : Function.Injective (LamQ2 M ζ hζ F B β hβeq hβ hB q) :=
  (LamQ2_spec M ζ hζ F B β hβeq hβ hB q).2

end LamQ2
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

end Reduce95
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

namespace Reduce95
open ExtCitation groupCohomology
open scoped groupCohomology

section levelMap

variable (F F₁ : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F] [NumberField ↥F₁] [IsGalois ℚ ↥F₁] (h : F ≤ F₁)

include h in
theorem comap_fixingSubgroup_le : F₁.fixingSubgroup.comap (MonoidHom.id _) ≤ F.fixingSubgroup.comap (MonoidHom.id _) := by
  intro s hs
  rw [Subgroup.mem_comap, IntermediateField.mem_fixingSubgroup_iff] at hs ⊢
  exact fun x hx => hs x (h hx)

noncomputable def levelMap : (↥F₁ ≃ₐ[ℚ] ↥F₁) →* (↥F ≃ₐ[ℚ] ↥F) :=
  ((groupCohomology.levelQuotientEquiv F).toMonoidHom.comp
    (QuotientGroup.map (F₁.fixingSubgroup.comap (MonoidHom.id _)) (F.fixingSubgroup.comap (MonoidHom.id _)) (MonoidHom.id _) (comap_fixingSubgroup_le F F₁ h))).comp
    (groupCohomology.levelQuotientEquiv F₁).symm.toMonoidHom

theorem levelMap_restrictNormalHom (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    levelMap F F₁ h (AlgEquiv.restrictNormalHom ↥F₁ γ) = AlgEquiv.restrictNormalHom ↥F γ := by
  have h1 : (groupCohomology.levelQuotientEquiv F₁).symm (AlgEquiv.restrictNormalHom ↥F₁ γ) = QuotientGroup.mk γ :=
    (MulEquiv.symm_apply_eq _).mpr (groupCohomology.levelQuotientEquiv_mk F₁ γ).symm
  change groupCohomology.levelQuotientEquiv F (QuotientGroup.map (F₁.fixingSubgroup.comap (MonoidHom.id _)) (F.fixingSubgroup.comap (MonoidHom.id _))
    (MonoidHom.id _) (comap_fixingSubgroup_le F F₁ h)
    ((groupCohomology.levelQuotientEquiv F₁).symm (AlgEquiv.restrictNormalHom ↥F₁ γ))) = _
  rw [h1, QuotientGroup.map_mk]
  exact groupCohomology.levelQuotientEquiv_mk F γ

theorem levelMap_surjective : Function.Surjective (levelMap F F₁ h) := by
  intro σ
  obtain ⟨g, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := ℚ) (K₁ := ↥F) (AlgebraicClosure ℚ) σ
  exact ⟨AlgEquiv.restrictNormalHom ↥F₁ g, levelMap_restrictNormalHom F F₁ h g⟩

variable {p : ℕ} [Fact p.Prime] (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) [FiniteDimensional (ZMod p) M]

noncomputable abbrev Bof₁ : Rep ℤ (↥F₁ ≃ₐ[ℚ] ↥F₁) := Rep.res (levelMap F F₁ h) (Bof M F)

noncomputable scoped instance fintype_Bof₁ : Fintype (Bof₁ F F₁ h M) := fintype_Bof M F

theorem betaOf_equivariant₁ (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (b : Bof₁ F F₁ h M) :
    betaOf M F ((Bof₁ F F₁ h M).ρ (AlgEquiv.restrictNormalHom ↥F₁ γ) b) = (M.dualTwist (cycloChar p)).ρ γ (betaOf M F b) := by
  change betaOf M F ((Bof M F).ρ (levelMap F F₁ h (AlgEquiv.restrictNormalHom ↥F₁ γ)) b) = _
  rw [levelMap_restrictNormalHom]
  exact betaOf_equivariant M F γ b

theorem Bof₁_torsion : ∀ b : Bof₁ F F₁ h M, p • b = 0 := Bof_torsion M F

variable {F₁} (π : (↥F₁ ≃ₐ[ℚ] ↥F₁) →* (↥F ≃ₐ[ℚ] ↥F))
  (hπ : ∀ γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, π (AlgEquiv.restrictNormalHom ↥F₁ γ) = AlgEquiv.restrictNormalHom ↥F γ)

noncomputable abbrev Bofπ : Rep ℤ (↥F₁ ≃ₐ[ℚ] ↥F₁) := Rep.res π (Bof M F)

noncomputable scoped instance fintype_Bofπ : Fintype (Bofπ F M π) := fintype_Bof M F

include hπ in
theorem betaOf_equivariantπ (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (b : Bofπ F M π) :
    betaOf M F ((Bofπ F M π).ρ (AlgEquiv.restrictNormalHom ↥F₁ γ) b) = (M.dualTwist (cycloChar p)).ρ γ (betaOf M F b) := by
  change betaOf M F ((Bof M F).ρ (π (AlgEquiv.restrictNormalHom ↥F₁ γ)) b) = _
  rw [hπ]
  exact betaOf_equivariant M F γ b

theorem Bofπ_torsion : ∀ b : Bofπ F M π, p • b = 0 := Bof_torsion M F

theorem levelMap_comp_restrictNormalHom (F₂ : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F₂] [IsGalois ℚ ↥F₂] (h₁₂ : F₁ ≤ F₂)
    (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    ((levelMap F F₁ h).comp (levelMap F₁ F₂ h₁₂)) (AlgEquiv.restrictNormalHom ↥F₂ γ) = AlgEquiv.restrictNormalHom ↥F γ := by
  rw [MonoidHom.comp_apply, levelMap_restrictNormalHom, levelMap_restrictNormalHom]

end levelMap
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

end Reduce95
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

namespace Reduce95
open ExtCitation groupCohomology GroupCohomology M4aHerbrand

section hIDcomp
open scoped Classical

variable {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes)
  (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) [FiniteDimensional (ZMod p) M]
  (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p)
  (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F] [IsTotallyComplex ↥F]
  (hζF : ζ ∈ F)
  (hunr : ∀ w : HeightOneSpectrum (𝓞 ↥F), w ∉ TT S F → Ideal.ramificationIdx' (w.asIdeal.under (𝓞 ℚ)) w.asIdeal = 1)
  (B : Rep ℤ (↥F ≃ₐ[ℚ] ↥F)) [Fintype B] (β : B →+ M.dualTwist (cycloChar p))
  (hβeq : ∀ (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (b : B),
    β (B.ρ (AlgEquiv.restrictNormalHom ↥F γ) b) = (M.dualTwist (cycloChar p)).ρ γ (β b))
  (hβ : Function.Bijective β) (hB : ∀ b : B, p • b = 0)
  (hp2 : p ≠ 2)
  (θ : ∀ v : extArithIndex S,
    continuousH1 (extArithLoc S v) (Rep.res (extArithLoc S v) M) →ₗ[ZMod p]
      Module.Dual (ZMod p) (continuousH1 (extArithLoc S v) (Rep.res (extArithLoc S v) (M.dualTwist (cycloChar p)))))
  (hθ : ∀ q : ↥S, haveI : Fact (((q : Nat.Primes) : ℕ)).Prime := ⟨(q : Nat.Primes).prop⟩
      IsTheta1 (extArithLoc S (Sum.inr q))
        (Module.Dual.eval (ZMod p) M :
          Rep.res (extArithLoc S (Sum.inr q)) M →ₗ[ZMod p]
            Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p)) →ₗ[ZMod p]
              ofChar (k := ZMod p) ((cycloChar p).comp (extArithLoc S (Sum.inr q))))
        (localInv p ζ (q : Nat.Primes)) (θ (Sum.inr q)))
  (hloc : ∀ y ∈ continuousH1S S (M.dualTwist (cycloChar p)), ∀ v : extArithIndex S,
    locTotal (extArithLoc S) (M.dualTwist (cycloChar p)) y v ∈ continuousH1 (extArithLoc S v) (Rep.res (extArithLoc S v) (M.dualTwist (cycloChar p))))
  (infl : ↥(groupCohomology B 1) →+ H1 (M.dualTwist (cycloChar p)))
  (hinflpin : ∀ (n : cocycles₁ B) (ny : cocycles₁ (M.dualTwist (cycloChar p))),
      (∀ γ, ny γ = β (n (AlgEquiv.restrictNormalHom ↥F γ))) →
        infl ((H1π B).hom n) = (H1π (M.dualTwist (cycloChar p))).hom ny)

  {VB₀ : Type} [AddCommGroup VB₀] (infl₀ : VB₀ →+ H1 (M.dualTwist (cycloChar p))) (ι : VB₀ →+ ↥(groupCohomology B 1))
  (hcomp : ∀ x, infl (ι x) = infl₀ x)

end hIDcomp
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

end Reduce95
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

namespace Reduce95
open ExtCitation groupCohomology GroupCohomology M4aHerbrand

section lesGlue

theorem map_f_delta_eq_zero {G : Type} [Group G] {X : ShortComplex (Rep ℤ G)} (hX : X.ShortExact) (i j : ℕ) (hij : i + 1 = j)
    (y : groupCohomology X.X₃ i) :
    (groupCohomology.map (MonoidHom.id G) X.f j).hom ((groupCohomology.δ hX i j hij).hom y) = 0 := by
  have h := (groupCohomology.mapShortComplex₁ hX hij).zero
  have := congrArg (fun φ => (ModuleCat.Hom.hom φ) y) h
  first | simpa using this | exact this | (simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply] at this; exact this)

variable {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes)
  (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F]
  (hunr : ∀ w : HeightOneSpectrum (𝓞 ↥F), w ∉ TT S F → Ideal.ramificationIdx' (w.asIdeal.under (𝓞 ℚ)) w.asIdeal = 1)
  (B : Rep ℤ (↥F ≃ₐ[ℚ] ↥F)) [Fintype B] (hB : ∀ b : B, p • b = 0)

theorem map_iEJ_dY' (t : Rep.relationModuleInt B ⟶ (seqF S F).X₃) :
    (groupCohomology.map (MonoidHom.id _) ((ihom (Rep.relationModuleInt B)).map (seqF S F).f) 1).hom (dY' S F B t) = 0 := by
  rw [dY'_apply]
  exact map_f_delta_eq_zero (hT' S F B) 0 1 rfl _

theorem dY'_add_ι_comp (t : Rep.relationModuleInt B ⟶ (seqF S F).X₃) (χ : Rep.free ℤ (↥F ≃ₐ[ℚ] ↥F) B ⟶ (seqF S F).X₃) :
    dY' S F B (t + Rep.relationModuleInt.ι B ≫ χ) = dY' S F B t := by
  haveI : Epi (seqF S F).g := (seqF_shortExact S F).epi_g
  rw [map_add]
  suffices h : dY' S F B (Rep.relationModuleInt.ι B ≫ χ) = 0 by rw [h, add_zero]
  have hfac : Rep.relationModuleInt.ι B ≫ χ = (Rep.relationModuleInt.ι B ≫ Projective.factorThru χ (seqF S F).g) ≫ (seqF S F).g := by
    rw [Category.assoc, Projective.factorThru_comp]
  rw [hfac]
  exact hLESc' S F B _

end lesGlue
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

end Reduce95
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

set_option autoImplicit false
open CategoryTheory groupCohomology IsDedekindDomain NumberField

namespace Reduce95
open ExtCitation M4aHerbrand GroupCohomology
open scoped NumberField.PlaceDecomp

section K0
variable {p : ℕ} [Fact p.Prime]

theorem finite_archimedeanDecomposition : Finite ↥archimedeanDecomposition := by
  have h : IsOfFinOrder complexConjugation := isOfFinOrder_iff_pow_eq_one.2 ⟨2, two_pos, complexConjugation_sq⟩
  change Finite ↥(Subgroup.zpowers complexConjugation)
  exact h.finite_zpowers

theorem natCard_archimedeanDecomposition_dvd_two : Nat.card ↥archimedeanDecomposition ∣ 2 := by
  change Nat.card ↥(Subgroup.zpowers complexConjugation) ∣ 2
  rw [Nat.card_zpowers]
  exact orderOf_dvd_of_pow_eq_one complexConjugation_sq

theorem H2_archimedean_eq_zero (hp2 : p ≠ 2) (A : Rep (ZMod p) ↥archimedeanDecomposition) (x : H2 A) : x = 0 := by
  classical
  haveI : Finite ↥archimedeanDecomposition := finite_archimedeanDecomposition
  haveI : Fintype ↥archimedeanDecomposition := Fintype.ofFinite _
  have hx := Rep.card_smul_eq_zero_of_tateCohomology A ((1 + 1 : ℕ) : ℤ) (show ↥(A.tateCohomology ((1 + 1 : ℕ) : ℤ)) from x)
  have hcop : (Fintype.card ↥archimedeanDecomposition).Coprime p := by
    rw [Fintype.card_eq_nat_card]
    exact Nat.Coprime.coprime_dvd_left natCard_archimedeanDecomposition_dvd_two
      ((Nat.coprime_primes Nat.prime_two Fact.out).2 (Ne.symm hp2))
  have hu : IsUnit ((Fintype.card ↥archimedeanDecomposition : ZMod p)) := (ZMod.isUnit_iff_coprime _ _).2 hcop
  exact (hu.smul_eq_zero).1 hx

theorem continuousH2_archimedeanLoc_eq_zero (hp2 : p ≠ 2) (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (F' : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥F']
    (hlev : ∀ s : ↥archimedeanDecomposition, archimedeanLoc s ∈ F'.fixingSubgroup → s = 1)
    (z : continuousH2 archimedeanLoc (Rep.res archimedeanLoc M)) : z = 0 := by
  classical
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  have h2 := H2_archimedean_eq_zero hp2 (Rep.res archimedeanLoc M)
    ((H2π (Rep.res archimedeanLoc M)).hom (levelCocyclesToCocycles₂ archimedeanLoc (Rep.res archimedeanLoc M) f))
  rw [H2π_eq_zero_iff] at h2
  obtain ⟨x, hx⟩ := h2
  change continuousH2π archimedeanLoc (Rep.res archimedeanLoc M) f = 0
  rw [continuousH2π_eq_zero_iff, mem_levelCoboundaries₂_iff]
  exact ⟨x, ⟨F', inferInstance, fun g s hs => by rw [hlev s hs, mul_one]⟩, hx⟩

end K0
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

section K2
variable {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes)
  (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F]
  (B : Rep ℤ (↥F ≃ₐ[ℚ] ↥F))

noncomputable abbrev toFibre (v : extArithIndex S) : (seqF S F).X₁ ⟶ J0fam S F v :=
  (seqF S F).f ≫ rHom S F ≫ RepPi.proj (J0fam S F) v

noncomputable abbrev shap (v : extArithIndex S) :
    Rep.res (Dv S F v).subtype ((ihom (Rep.relationModuleInt B)).obj (J0fam S F v)) ⟶
      (ihom (Rep.res (Dv S F v).subtype (Rep.relationModuleInt B))).obj (Yv S F v) :=
  Rep.resIhom (Dv S F v).subtype (Rep.relationModuleInt B) (J0fam S F v) ≫
    (ihom (Rep.res (Dv S F v).subtype (Rep.relationModuleInt B))).map ((Rep.resCoindAdjunction ℤ (Dv S F v).subtype).counit.app (Yv S F v))

noncomputable def aV (a : cocycles₁ ((ihom (Rep.relationModuleInt B)).obj (seqF S F).X₁)) (v : extArithIndex S) :
    cocycles₁ ((ihom (Rep.res (Dv S F v).subtype (Rep.relationModuleInt B))).obj (Yv S F v)) :=
  (mapCocycles₁ (Dv S F v).subtype (shap S F B v)).hom
    ((mapCocycles₁ (MonoidHom.id (↥F ≃ₐ[ℚ] ↥F)) ((ihom (Rep.relationModuleInt B)).map (RepPi.proj (J0fam S F) v))).hom
      ((mapCocycles₁ (MonoidHom.id (↥F ≃ₐ[ℚ] ↥F)) ((ihom (Rep.relationModuleInt B)).map (rHom S F))).hom
        ((mapCocycles₁ (MonoidHom.id (↥F ≃ₐ[ℚ] ↥F)) ((ihom (Rep.relationModuleInt B)).map (seqF S F).f)).hom a)))

theorem shap_component (a : cocycles₁ ((ihom (Rep.relationModuleInt B)).obj (seqF S F).X₁)) (v : extArithIndex S) :
    (groupCohomology.map (Dv S F v).subtype (shap S F B v) 1).hom
      ((groupCohomology.map (MonoidHom.id (↥F ≃ₐ[ℚ] ↥F)) ((ihom (Rep.relationModuleInt B)).map (RepPi.proj (J0fam S F) v)) 1).hom
        ((groupCohomology.map (MonoidHom.id (↥F ≃ₐ[ℚ] ↥F)) ((ihom (Rep.relationModuleInt B)).map (rHom S F)) 1).hom
          ((groupCohomology.map (MonoidHom.id (↥F ≃ₐ[ℚ] ↥F)) ((ihom (Rep.relationModuleInt B)).map (seqF S F).f) 1).hom
            ((H1π ((ihom (Rep.relationModuleInt B)).obj (seqF S F).X₁)).hom a)))) = (H1π _).hom (aV S F B a v) := by
  simp only [H1π_comp_map_apply]
  rfl

set_option synthInstance.maxHeartbeats 3200000 in

theorem toMul_aV_inr (a : cocycles₁ ((ihom (Rep.relationModuleInt B)).obj (seqF S F).X₁)) (q : ↥S)
    (d : ↥(Dv S F (Sum.inr q))) (x : Rep.relationModuleInt B) :
    Additive.toMul (LinearMap.toAddMonoidHom ((aV S F B a (Sum.inr q) : ↥(Dv S F (Sum.inr q)) → _) d) x) =
      Units.map (algebraMap ↥F ((wq F q.1).adicCompletion ↥F) : ↥F →* (wq F q.1).adicCompletion ↥F)
        (NumberField.SUnits.val ℚ ↥F (Sq S) (LinearMap.toAddMonoidHom ((a : (↥F ≃ₐ[ℚ] ↥F) → _) (d : ↥F ≃ₐ[ℚ] ↥F)) x)) := by
  change Additive.toMul (((NumberField.SUnits.diagIn ℚ ↥F (Sq S) (eS S q)).hom
    (LinearMap.toAddMonoidHom ((a : (↥F ≃ₐ[ℚ] ↥F) → _) (d : ↥F ≃ₐ[ℚ] ↥F)) x)).1 1) = _
  rw [NumberField.SUnits.diagIn_hom_apply_apply, one_smul]
  rfl

end K2
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

section K3
local instance factPrimesE2' (q : Nat.Primes) : Fact ((q : ℕ)).Prime := ⟨q.2⟩

variable {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
  (M : Rep.{0} (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) [FiniteDimensional (ZMod p) M]
  (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p)
  (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F] [IsTotallyComplex ↥F]
  (hFS : F.IsUnramifiedOutside S) (hζF : ζ ∈ F)
  (B : Rep ℤ (↥F ≃ₐ[ℚ] ↥F)) [Fintype B] (β : B →+ M.dualTwist (cycloChar p))
  (hβeq : ∀ (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (b : B),
    β (B.ρ (AlgEquiv.restrictNormalHom ↥F γ) b) = (M.dualTwist (cycloChar p)).ρ γ (β b))
  (hβ : Function.Bijective β) (hB : ∀ b : B, p • b = 0) (hp2 : p ≠ 2)

include hβeq hβ hB in
set_option maxHeartbeats 16000000 in

theorem square_inr (a : cocycles₁ ((ihom (Rep.relationModuleInt B)).obj (seqF S F).X₁)) (q : ↥S) :
    locRes₂S S M (extArithLoc S (Sum.inr q)) (LE2' S hpS M ζ hζ F hFS B β hβeq hβ hB ((H1π ((ihom (Rep.relationModuleInt B)).obj (seqF S F).X₁)).hom a)) =
      LamQ2 M ζ hζ F B β hβeq hβ hB q.1 ((H1π _).hom (aV S F B a (Sum.inr q))) :=
  NumberField.SUnits.locRes2S_isGlobalBridge2_apply_eq_of_finite S q hpS (Sq S) (coe_Sq S) M F hFS (wq F q.1) (sigmaQ F q.1) (PhiQ F q.1)
    (hPhiF_q F q.1) (hcont_q F q.1) (piQ F q.1) (hpi_q F q.1) (heqv_q F q.1)
    (Rep.relationModuleInt.ι B) (Rep.freeCover B) (relationModuleInt_ι_injective B) (exact_ι_freeCover B) (freeCover_surjective B)
    hB (iotaE F (Sq S)) (toMul_iotaE F (Sq S)) (kappa M ζ hζ B β) (kappa_equivariant M ζ hζ (AlgEquiv.restrictNormalHom ↥F) B β hβeq)
    (kappa_perfect M ζ hζ B β hβ hB) (kappaQF M F q.1 B (kappa M ζ hζ B β))
    (toMul_kappaQ M ((q : Nat.Primes) : ℕ) (sigmaQ F q.1) B (kappa M ζ hζ B β))
    (LE2'_spec S hpS M ζ hζ F hFS B β hβeq hβ hB) (LamQ2_bridge M ζ hζ F B β hβeq hβ hB q.1) a (aV S F B a (Sum.inr q))
    (toMul_aV_inr S F B a q)

theorem map_rInv_map_rHom (y : H1 ((ihom (Rep.relationModuleInt B)).obj (seqF S F).X₂)) :
    (groupCohomology.map (MonoidHom.id (↥F ≃ₐ[ℚ] ↥F)) (A := (ihom (Rep.relationModuleInt B)).obj (RepPi.obj (J0fam S F)))
        ((ihom (Rep.relationModuleInt B)).map (rInv S F)) 1).hom
      ((groupCohomology.map (MonoidHom.id (↥F ≃ₐ[ℚ] ↥F)) (A := (ihom (Rep.relationModuleInt B)).obj (seqF S F).X₂)
        ((ihom (Rep.relationModuleInt B)).map (rHom S F)) 1).hom y) = y := by
  have key : groupCohomology.map (MonoidHom.id (↥F ≃ₐ[ℚ] ↥F)) (A := (ihom (Rep.relationModuleInt B)).obj (seqF S F).X₂)
        ((ihom (Rep.relationModuleInt B)).map (rHom S F)) 1 ≫
      groupCohomology.map (MonoidHom.id (↥F ≃ₐ[ℚ] ↥F)) (A := (ihom (Rep.relationModuleInt B)).obj (RepPi.obj (J0fam S F)))
        ((ihom (Rep.relationModuleInt B)).map (rInv S F)) 1 = 𝟙 _ := by
    rw [← groupCohomology.map_id_comp, ← CategoryTheory.Functor.map_comp]
    show groupCohomology.map (MonoidHom.id (↥F ≃ₐ[ℚ] ↥F))
        (A := (ihom (Rep.relationModuleInt B)).obj (NumberField.SArchIdele.obj ℚ ↥F (Sq S)))
        ((ihom (Rep.relationModuleInt B)).map (rHom S F ≫ rInv S F)) 1 =
      𝟙 (groupCohomology ((ihom (Rep.relationModuleInt B)).obj (NumberField.SArchIdele.obj ℚ ↥F (Sq S))) 1)
    rw [rHom_rInv, CategoryTheory.Functor.map_id, groupCohomology.map_id]
  exact congrArg (fun φ => φ.hom y) key

theorem map_rHom_injective :
    Function.Injective (groupCohomology.map (MonoidHom.id (↥F ≃ₐ[ℚ] ↥F))
      (A := (ihom (Rep.relationModuleInt B)).obj (seqF S F).X₂)
      ((ihom (Rep.relationModuleInt B)).map (rHom S F)) 1).hom :=
  Function.LeftInverse.injective (map_rInv_map_rHom S F B)

include hζ hζF hβeq hβ hB hp2 in

theorem H1_arch_eq_zero (u : Unit)
    (z : H1 ((ihom (Rep.res (Dv S F (Sum.inl u)).subtype (Rep.relationModuleInt B))).obj (Yv S F (Sum.inl u)))) : z = 0 := by
  haveI : Finite B := inferInstance
  obtain ⟨Λi, -, hinj⟩ := NumberField.InfPlaceDecomp.exists_isLocalBridge2_archimedean M F (winf F) (sigmaInf F) (piInf F) (hpi_inf F)
    (piInf_bijective F) (hσF_inf F) (Rep.relationModuleInt.ι B) (Rep.freeCover B) (relationModuleInt_ι_injective B)
    (exact_ι_freeCover B) (freeCover_surjective B) B (Iso.refl _) hB (kappaInf M ζ hζ F hζF B β)
    (kappaInf_eqv M ζ hζ F hζF B β hβeq) (kappaInf_perfect M ζ hζ F hζF B β hβ hB)
  apply hinj
  exact (continuousH2_archimedeanLoc_eq_zero hp2 M F
    (NumberField.InfPlaceDecomp.localBridge_hypotheses_archimedean F (winf F) (sigmaInf F) (piInf F) (hpi_inf F)
      (piInf_bijective F) (hσF_inf F)).1 _).trans (map_zero Λi).symm

include hζ hζF hp2 in
set_option maxHeartbeats 16000000 in

theorem hKERLOC_F (x : H1 ((ihom (Rep.relationModuleInt B)).obj (seqF S F).X₁))
    (h : ∀ v, locRes₂S S M (extArithLoc S v) (LE2' S hpS M ζ hζ F hFS B β hβeq hβ hB x) = 0) :
    (groupCohomology.map (MonoidHom.id (↥F ≃ₐ[ℚ] ↥F)) ((ihom (Rep.relationModuleInt B)).map (seqF S F).f) 1).hom x = 0 := by
  classical
  obtain ⟨a, ha⟩ := (ModuleCat.epi_iff_surjective (H1π _)).1 inferInstance x
  have ha' : (H1π ((ihom (Rep.relationModuleInt B)).obj (seqF S F).X₁)).hom a = x := ha
  subst ha'
  apply map_rHom_injective S F B
  refine Eq.trans ?_ (map_zero _).symm
  refine (GroupCohomology.RepPi.map_ihom_proj_one_injective_and_surjective (J0fam S F) (Rep.relationModuleInt B)).1 _ fun v => ?_
  apply (groupCohomology.map_resIhom_comp_ihom_map_counit_one_bijective (Dv S F v) (Rep.relationModuleInt B) (Yv S F v)).1
  refine Eq.trans ?_ (map_zero _).symm
  refine (shap_component S F B a v).trans ?_
  rcases v with u | q
  · exact H1_arch_eq_zero S M ζ hζ F hζF B β hβeq hβ hB hp2 u _
  · exact LamQ2_injective M ζ hζ F B β hβeq hβ hB q.1
      (((square_inr S hpS M ζ hζ F hFS B β hβeq hβ hB a q).symm.trans (h (Sum.inr q))).trans (map_zero _).symm)

include hζ hζF hp2 in
set_option maxHeartbeats 16000000 in

theorem hKERLOC'_F (x : H1 ((ihom (Rep.relationModuleInt B)).obj (seqF S F).X₁))
    (hx : (groupCohomology.map (MonoidHom.id (↥F ≃ₐ[ℚ] ↥F)) ((ihom (Rep.relationModuleInt B)).map (seqF S F).f) 1).hom x = 0)
    (v : extArithIndex S) : locRes₂S S M (extArithLoc S v) (LE2' S hpS M ζ hζ F hFS B β hβeq hβ hB x) = 0 := by
  classical
  obtain ⟨a, ha⟩ := (ModuleCat.epi_iff_surjective (H1π _)).1 inferInstance x
  have ha' : (H1π ((ihom (Rep.relationModuleInt B)).obj (seqF S F).X₁)).hom a = x := ha
  subst ha'
  rcases v with u | q
  · exact continuousH2_archimedeanLoc_eq_zero hp2 M F
      (NumberField.InfPlaceDecomp.localBridge_hypotheses_archimedean F (winf F) (sigmaInf F) (piInf F) (hpi_inf F)
        (piInf_bijective F) (hσF_inf F)).1 _
  · refine (square_inr S hpS M ζ hζ F hFS B β hβeq hβ hB a q).trans ?_
    refine (congrArg (LamQ2 M ζ hζ F B β hβeq hβ hB q.1) (shap_component S F B a (Sum.inr q)).symm).trans ?_
    rw [hx, LinearMap.map_zero, LinearMap.map_zero, LinearMap.map_zero]
    exact map_zero _

end K3
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

end Reduce95
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

set_option autoImplicit false
open CategoryTheory groupCohomology

namespace Reduce95

section H0currency
variable {G : Type} [Group G]

noncomputable def U0 (A : Rep ℤ G) (z : H0 A) : A := (((H0Iso A).hom z : A.ρ.invariants) : A)

theorem U0_injective (A : Rep ℤ G) : Function.Injective (U0 A) := by
  intro z z' h
  have h1 : (H0Iso A).hom z = (H0Iso A).hom z' := Subtype.ext h
  have h2 := congrArg (H0Iso A).inv h1
  simpa only [Iso.hom_inv_id_apply] using h2

theorem U0_map {H : Type} [Group H] {A : Rep ℤ H} {B : Rep ℤ G} (f : G →* H) (φ : Rep.res f A ⟶ B) (z : H0 A) :
    U0 B ((groupCohomology.map f φ 0).hom z) = φ.hom (U0 A z) := by
  have h := congrArg (fun ψ => ψ.hom z) (groupCohomology.map_H0Iso_hom_f f φ)
  exact h

noncomputable def toH0 (R X : Rep ℤ G) (t : R ⟶ X) : H0 ((ihom R).obj X) :=
  (H0Iso ((ihom R).obj X)).inv ((Representation.linHom.invariantsEquivRepHom R X).symm t)

theorem U0_toH0 (R X : Rep ℤ G) (t : R ⟶ X) :
    U0 ((ihom R).obj X) (toH0 R X t) = (show (ihom R).obj X from ((Representation.linHom.invariantsEquivRepHom R X).symm t :
      ((ihom R).obj X).ρ.invariants).1) := by
  unfold U0 toH0
  rw [Iso.inv_hom_id_apply]

theorem U0_toH0_apply (R X : Rep ℤ G) (t : R ⟶ X) (r : R) :
    (show R →ₗ[ℤ] X from U0 ((ihom R).obj X) (toH0 R X t)) r = t.hom r := by
  rw [U0_toH0]
  rfl

noncomputable def ofH0 (R X : Rep ℤ G) (z : H0 ((ihom R).obj X)) : R ⟶ X :=
  Representation.linHom.invariantsEquivRepHom R X ((H0Iso ((ihom R).obj X)).hom z)

theorem ofH0_hom_apply (R X : Rep ℤ G) (z : H0 ((ihom R).obj X)) (r : R) :
    (ofH0 R X z).hom r = (show R →ₗ[ℤ] X from U0 ((ihom R).obj X) z) r := rfl

end H0currency
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

section PIT
variable {G G' : Type} [Group G] [Group G'] [Fintype G] [Fintype G'] (π : G' →* G) (B : Rep ℤ G) (p : ℕ) [Fact p.Prime]
  (hB : ∀ b : B, p • b = 0)
  {T : ShortComplex (Rep ℤ G)} (hT : T.ShortExact) {T' : ShortComplex (Rep ℤ G')} (hT' : T'.ShortExact) [Finite T.X₃] [Finite T'.X₃]
  (φ₁ : Rep.res π T.X₁ ⟶ T'.X₁) (φ₂ : Rep.res π T.X₂ ⟶ T'.X₂) (φ₃ : Rep.res π T.X₃ ⟶ T'.X₃)
  (w₁ : (Rep.resFunctor π).map T.f ≫ φ₂ = φ₁ ≫ T'.f) (w₂ : (Rep.resFunctor π).map T.g ≫ φ₃ = φ₂ ≫ T'.g)
  (hpit : ∀ c : T.X₃, (∃ k : ℕ, p ^ k • c = 0) → φ₃.hom c = 0)

include hB hT hT' w₁ w₂ hpit in

theorem hPITco_gen (iC : (Rep.relationModuleInt B ⟶ T.X₂) → (Rep.relationModuleInt (Rep.res π B) ⟶ T'.X₂))
    (hiC : ∀ φ, iC φ = Rep.relationModuleInt.resMap π B ≫ (Rep.resFunctor π).map φ ≫ φ₂)
    (φ : Rep.relationModuleInt B ⟶ T.X₂) :
    ∃ (t : Rep.relationModuleInt (Rep.res π B) ⟶ T'.X₁) (χ : Rep.free ℤ G' (Rep.res π B) ⟶ T'.X₂),
      iC φ = t ≫ T'.f + Rep.relationModuleInt.ι (Rep.res π B) ≫ χ := by
  obtain ⟨t, χ, h⟩ := Rep.exists_resMap_comp_eq_comp_add_iota_comp_of_pit π B p hB hT hT' φ₁ φ₂ φ₃ w₁ w₂ hpit φ
  exact ⟨t, χ, (hiC φ).trans h⟩

include hB hT hT' w₁ w₂ hpit in

theorem hPITker_gen (iY : (Rep.relationModuleInt B ⟶ T.X₁) → (Rep.relationModuleInt (Rep.res π B) ⟶ T'.X₁))
    (hiY : ∀ t, iY t = Rep.relationModuleInt.resMap π B ≫ (Rep.resFunctor π).map t ≫ φ₁)
    (t : Rep.relationModuleInt B ⟶ T.X₁) (χ : Rep.free ℤ G B ⟶ T.X₂)
    (h : t ≫ T.f = Rep.relationModuleInt.ι B ≫ χ) :
    ∃ χ' : Rep.free ℤ G' (Rep.res π B) ⟶ T'.X₁, iY t = Rep.relationModuleInt.ι (Rep.res π B) ≫ χ' := by

  have hz : ∃ ψ : groupCohomology ((ihom (Rep.free ℤ G B)).obj T.X₂) 0,
      (groupCohomology.map (MonoidHom.id G) (Rep.preι B T.X₂) 0).hom ψ =
        (groupCohomology.map (MonoidHom.id G) ((ihom (Rep.relationModuleInt B)).map T.f) 0).hom (toH0 _ _ t) := by
    refine ⟨toH0 _ _ χ, U0_injective _ ?_⟩
    rw [U0_map, U0_map]
    apply LinearMap.ext
    intro r
    change (show Rep.free ℤ G B →ₗ[ℤ] T.X₂ from U0 _ (toH0 _ _ χ)) ((Rep.relationModuleInt.ι B).hom r) =
      T.f.hom ((show Rep.relationModuleInt B →ₗ[ℤ] T.X₁ from U0 _ (toH0 _ _ t)) r)
    rw [U0_toH0_apply, U0_toH0_apply]
    exact (congrArg (fun ψ : Rep.relationModuleInt B ⟶ T.X₂ => ψ.hom r) h).symm

  obtain ⟨ψ', hψ'⟩ := Rep.exists_preIota_eq_map_extInflR_zero_of_exists_preIota_eq_of_pit π B p hB hT hT' φ₁ φ₂ φ₃ w₁ w₂ hpit
    (toH0 _ _ t) hz
  refine ⟨ofH0 _ _ ψ', Rep.hom_ext (DFunLike.ext _ _ fun r => ?_)⟩
  have hU := congrArg (U0 _) hψ'
  rw [U0_map, U0_map] at hU
  have hr := LinearMap.congr_fun hU r

  rw [hiY]
  change φ₁.hom (t.hom ((Rep.relationModuleInt.resMap π B).hom r)) = (ofH0 _ _ ψ').hom ((Rep.relationModuleInt.ι (Rep.res π B)).hom r)
  rw [ofH0_hom_apply]
  refine Eq.trans ?_ hr.symm
  change _ = φ₁.hom ((show Rep.relationModuleInt B →ₗ[ℤ] T.X₁ from U0 _ (toH0 _ _ t)) ((Rep.relationModuleInt.resMap π B).hom r))
  rw [U0_toH0_apply]

end PIT
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

end Reduce95
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

namespace Reduce95
open ExtCitation groupCohomology
open scoped groupCohomology

section sLevelTools

variable (S : Finset Nat.Primes)

theorem exists_isGalois_sLevel_ge (F₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (h₀ : F₀.IsUnramifiedOutside S) :
    ∃ (F : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : NumberField ↥F) (_ : IsGalois ℚ ↥F), F₀ ≤ F ∧ F.IsUnramifiedOutside S := by
  obtain ⟨L, hle, hL, hnorm⟩ := IntermediateField.exists_normal_isUnramifiedOutside_of_le S F₀ h₀
  haveI : FiniteDimensional ℚ ↥L := hL.1
  haveI : Normal ℚ ↥L := hnorm
  haveI : NumberField ↥L := ⟨⟩
  haveI : IsGalois ℚ ↥L := ⟨⟩
  exact ⟨L, inferInstance, inferInstance, hle, hL⟩

variable {p : ℕ} [Fact p.Prime] (hpS : pPrime p ∈ S)

theorem exists_prim_sq : ∃ ζ₂ : AlgebraicClosure ℚ, IsPrimitiveRoot ζ₂ (p ^ 2) := by
  haveI : NeZero ((p ^ 2 : ℕ) : AlgebraicClosure ℚ) := NeZero.charZero
  exact HasEnoughRootsOfUnity.prim

theorem dvd_finrank_adjoin_prim_sq (ζ₂ : AlgebraicClosure ℚ) (hζ₂ : IsPrimitiveRoot ζ₂ (p ^ 2)) :
    p ∣ Module.finrank ℚ ↥(IntermediateField.adjoin ℚ ({ζ₂} : Set (AlgebraicClosure ℚ))) := by
  have hp : p.Prime := Fact.out
  have hint : IsIntegral ℚ ζ₂ := (hζ₂.isIntegral (pow_pos hp.pos 2)).tower_top
  rw [IntermediateField.adjoin.finrank hint]
  have hmin : minpoly ℚ ζ₂ = Polynomial.cyclotomic (p ^ 2) ℚ := by
    rw [← IsPrimitiveRoot.minpoly_eq_cyclotomic_of_irreducible hζ₂ (Polynomial.cyclotomic.irreducible_rat (pow_pos hp.pos 2))]
  rw [hmin, Polynomial.natDegree_cyclotomic, Nat.totient_prime_pow hp (by norm_num : 0 < 2)]
  exact dvd_mul_of_dvd_left (dvd_pow_self p (by norm_num)) _

include hpS in
theorem adjoin_prim_sq_isUnramifiedOutside (ζ₂ : AlgebraicClosure ℚ) (hζ₂ : IsPrimitiveRoot ζ₂ (p ^ 2)) :
    (IntermediateField.adjoin ℚ ({ζ₂} : Set (AlgebraicClosure ℚ))).IsUnramifiedOutside S :=
  IntermediateField.adjoin_isUnramifiedOutside_of_isPrimitiveRoot_pow S hpS 1 ζ₂ (by simpa using hζ₂)

include hpS in
theorem adjoin_prim_isUnramifiedOutside (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p) :
    (IntermediateField.adjoin ℚ ({ζ} : Set (AlgebraicClosure ℚ))).IsUnramifiedOutside S :=
  IntermediateField.adjoin_isUnramifiedOutside_of_isPrimitiveRoot_pow S hpS 0 ζ (by simpa using hζ)

theorem dvd_card_gal_of_le (ζ₂ : AlgebraicClosure ℚ) (hζ₂ : IsPrimitiveRoot ζ₂ (p ^ 2))
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥F] [IsGalois ℚ ↥F]
    (hle : IntermediateField.adjoin ℚ ({ζ₂} : Set (AlgebraicClosure ℚ)) ≤ F) : p ∣ Nat.card (↥F ≃ₐ[ℚ] ↥F) := by
  rw [IsGalois.card_aut_eq_finrank ℚ ↥F]
  exact (dvd_finrank_adjoin_prim_sq ζ₂ hζ₂).trans (IntermediateField.finrank_dvd_of_le_right hle)

end sLevelTools
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

end Reduce95
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

namespace Reduce95
open ExtCitation groupCohomology
open scoped groupCohomology

section baseLevel

variable {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
  (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) [FiniteDimensional (ZMod p) M]
  (hsm : ∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
    ∀ s ∈ F.fixingSubgroup, M.ρ s m = m)
  (hMur : ∀ q : Nat.Primes, q ∉ S → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
    A.LiesOverPrime (q : ℕ) → ∀ g ∈ A.inertiaSubgroupIn ℚ, M.ρ g = 1)
  (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p)
  [FiniteDimensional (ZMod p) ↥(continuousH1S S (M.dualTwist (cycloChar p)))]
  (Fx : IntermediateField ℚ (AlgebraicClosure ℚ)) (hFx : Fx.IsUnramifiedOutside S)

include hpS hsm hMur hζ hFx in
theorem exists_baseLevel : ∃ (F : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : NumberField ↥F) (_ : IsGalois ℚ ↥F),
    F.IsUnramifiedOutside S ∧ Fx ≤ F ∧
    (∀ s ∈ F.fixingSubgroup, ∀ m : M.dualTwist (cycloChar p), (M.dualTwist (cycloChar p)).ρ s m = m) ∧
    (∀ s ∈ F.fixingSubgroup, ∀ m : M, M.ρ s m = m) ∧
    (∀ x : H1 (M.dualTwist (cycloChar p)), x ∈ continuousH1S S (M.dualTwist (cycloChar p)) →
      ∃ ny : cocycles₁ (M.dualTwist (cycloChar p)), (H1π (M.dualTwist (cycloChar p))).hom ny = x ∧
        (∀ (γ s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), s ∈ F.fixingSubgroup → ny (γ * s) = ny γ) ∧
        (∀ s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, s ∈ F.fixingSubgroup → ny s = 0)) ∧
    ζ ∈ F ∧ p ∣ Nat.card (↥F ≃ₐ[ℚ] ↥F) := by

  obtain ⟨FM, hFMS, hFM⟩ := groupCohomology.exists_isUnramifiedOutside_forall_apply_eq_one_of_smooth S M hsm hMur

  have hsm' : ∀ m : M.dualTwist (cycloChar p), ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s ∈ F.fixingSubgroup, (M.dualTwist (cycloChar p)).ρ s m = m := fun x => by
    obtain ⟨F, hF, hFx⟩ := Rep.dualTwist_cycloChar_smooth M hsm (show M.dualTwist (cycloChar p) from x)
    exact ⟨F, hF, fun s hs => hFx _ hs⟩
  have hMur' := Rep.dualTwist_cycloChar_unramifiedOutside S hpS M hMur
  obtain ⟨FM', hFM'S, hFM'⟩ := groupCohomology.exists_isUnramifiedOutside_forall_apply_eq_one_of_smooth S (M.dualTwist (cycloChar p)) hsm' hMur'

  obtain ⟨ζ₂, hζ₂⟩ := exists_prim_sq (p := p)

  obtain ⟨Fst, _, _, hFstS, hstab⟩ := groupCohomology.exists_isGalois_forall_mem_continuousH1S_exists_cocyclesOne S (M.dualTwist (cycloChar p))

  have hF₀ : (FM ⊔ FM' ⊔ IntermediateField.adjoin ℚ ({ζ} : Set (AlgebraicClosure ℚ)) ⊔
      IntermediateField.adjoin ℚ ({ζ₂} : Set (AlgebraicClosure ℚ)) ⊔ Fst ⊔ Fx).IsUnramifiedOutside S :=
    ((((hFMS.sup hFM'S).sup (adjoin_prim_isUnramifiedOutside S hpS ζ hζ)).sup (adjoin_prim_sq_isUnramifiedOutside S hpS ζ₂ hζ₂)).sup hFstS).sup hFx
  obtain ⟨F, instNF, instG, hle, hFS⟩ := exists_isGalois_sLevel_ge S _ hF₀

  have iM : FM ≤ F := (le_sup_left.trans (le_sup_left.trans (le_sup_left.trans (le_sup_left.trans le_sup_left)))).trans hle
  have iM' : FM' ≤ F := (le_sup_right.trans (le_sup_left.trans (le_sup_left.trans (le_sup_left.trans le_sup_left)))).trans hle
  have iζ : IntermediateField.adjoin ℚ ({ζ} : Set (AlgebraicClosure ℚ)) ≤ F := (le_sup_right.trans (le_sup_left.trans (le_sup_left.trans le_sup_left))).trans hle
  have iζ₂ : IntermediateField.adjoin ℚ ({ζ₂} : Set (AlgebraicClosure ℚ)) ≤ F := (le_sup_right.trans (le_sup_left.trans le_sup_left)).trans hle
  have ist : Fst ≤ F := (le_sup_right.trans le_sup_left).trans hle
  have ix : Fx ≤ F := le_sup_right.trans hle
  refine ⟨F, instNF, instG, hFS, ix, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs m
    have h := hFM' s (IntermediateField.fixingSubgroup_antitone iM' hs)
    rw [h]; rfl
  · intro s hs m
    have h := hFM s (IntermediateField.fixingSubgroup_antitone iM hs)
    rw [h]; rfl
  · intro x hx
    obtain ⟨ny, h1, h2, h3⟩ := hstab x hx
    exact ⟨ny, h1, fun γ s hs => h2 γ s (IntermediateField.fixingSubgroup_antitone ist hs),
      fun s hs => h3 s (IntermediateField.fixingSubgroup_antitone ist hs)⟩
  · exact iζ (IntermediateField.mem_adjoin_simple_self ℚ ζ)
  · haveI : FiniteDimensional ℚ ↥F := inferInstance
    exact dvd_card_gal_of_le ζ₂ hζ₂ F iζ₂

end baseLevel
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

end Reduce95
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

namespace Reduce95
open ExtCitation groupCohomology

section levelMapR

variable (F F₁ : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F] [NumberField ↥F₁] [IsGalois ℚ ↥F₁] (h : F ≤ F₁)

noncomputable def inclAlg : Algebra ↥F ↥F₁ := (IntermediateField.inclusion h).toRingHom.toAlgebra

theorem inclAlg_algebraMap (x : ↥F) : (@algebraMap ↥F ↥F₁ _ _ (inclAlg F F₁ h) x : AlgebraicClosure ℚ) = (x : AlgebraicClosure ℚ) := rfl

theorem inclAlg_isScalarTower : @IsScalarTower ℚ ↥F ↥F₁ _ (inclAlg F F₁ h).toSMul _ := by
  letI := inclAlg F F₁ h
  exact IsScalarTower.of_algebraMap_eq (fun x => Subtype.ext rfl)

noncomputable def levelMapR : (↥F₁ ≃ₐ[ℚ] ↥F₁) →* (↥F ≃ₐ[ℚ] ↥F) :=
  letI := inclAlg F F₁ h
  letI := inclAlg_isScalarTower F F₁ h
  AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := ↥F₁) ↥F

theorem levelMapR_restrictNormalHom (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    levelMapR F F₁ h (AlgEquiv.restrictNormalHom ↥F₁ γ) = AlgEquiv.restrictNormalHom ↥F γ := by
  letI := inclAlg F F₁ h
  letI := inclAlg_isScalarTower F F₁ h
  apply AlgEquiv.ext
  intro x
  apply Subtype.ext
  have h1 : ((levelMapR F F₁ h (AlgEquiv.restrictNormalHom ↥F₁ γ) x : ↥F) : AlgebraicClosure ℚ) =
      ((AlgEquiv.restrictNormalHom ↥F₁ γ) (algebraMap ↥F ↥F₁ x) : AlgebraicClosure ℚ) := by
    have := AlgEquiv.restrictNormal_commutes (AlgEquiv.restrictNormalHom ↥F₁ γ) ↥F x
    exact (congrArg (fun y : ↥F₁ => (y : AlgebraicClosure ℚ)) this :)
  rw [h1]
  change ((AlgEquiv.restrictNormalHom ↥F₁ γ) (algebraMap ↥F ↥F₁ x) : AlgebraicClosure ℚ) = ((AlgEquiv.restrictNormalHom ↥F γ x : ↥F) : AlgebraicClosure ℚ)
  rw [show ((AlgEquiv.restrictNormalHom ↥F γ x : ↥F) : AlgebraicClosure ℚ) = γ (x : AlgebraicClosure ℚ) from AlgEquiv.restrictNormal_commutes γ ↥F x]
  have h2 := AlgEquiv.restrictNormal_commutes γ ↥F₁ (algebraMap ↥F ↥F₁ x)
  exact h2.trans (by rfl)

theorem levelMapR_surjective : Function.Surjective (levelMapR F F₁ h) := by
  intro σ
  letI := groupCohomology.isAlgClosure_rat_algebraicClosure
  obtain ⟨g, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := ℚ) (K₁ := ↥F) (AlgebraicClosure ℚ) σ
  exact ⟨AlgEquiv.restrictNormalHom ↥F₁ g, levelMapR_restrictNormalHom F F₁ h g⟩

theorem levelMapR_comp_restrictNormalHom (F₂ : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F₂] [IsGalois ℚ ↥F₂] (h₁₂ : F₁ ≤ F₂)
    (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    ((levelMapR F F₁ h).comp (levelMapR F₁ F₂ h₁₂)) (AlgEquiv.restrictNormalHom ↥F₂ γ) = AlgEquiv.restrictNormalHom ↥F γ := by
  rw [MonoidHom.comp_apply, levelMapR_restrictNormalHom, levelMapR_restrictNormalHom]

end levelMapR
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

end Reduce95
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

namespace Reduce95
open ExtCitation groupCohomology M4aHerbrand
open scoped NumberField.PlaceDecomp

section tower

variable (S : Finset Nat.Primes) (F F₁ : IntermediateField ℚ (AlgebraicClosure ℚ))
  [NumberField ↥F] [IsGalois ℚ ↥F] [NumberField ↥F₁] [IsGalois ℚ ↥F₁] [hle : Fact (F ≤ F₁)]

noncomputable scoped instance towerAlgebra : Algebra ↥F ↥F₁ := inclAlg F F₁ hle.out
scoped instance towerScalar : IsScalarTower ℚ ↥F ↥F₁ := inclAlg_isScalarTower F F₁ hle.out

theorem restrictNormalHom_eq_levelMapR : (AlgEquiv.restrictNormalHom ↥F : (↥F₁ ≃ₐ[ℚ] ↥F₁) →* (↥F ≃ₐ[ℚ] ↥F)) = levelMapR F F₁ hle.out := rfl

variable (J : AdeleRing (𝓞 ↥F) ↥F →+* AdeleRing (𝓞 ↥F₁) ↥F₁)
  (hJF : ∀ a : ↥F, J (algebraMap ↥F (AdeleRing (𝓞 ↥F) ↥F) a) = algebraMap ↥F₁ (AdeleRing (𝓞 ↥F₁) ↥F₁) (algebraMap ↥F ↥F₁ a))
  (hJeq : ∀ (g' : ↥F₁ ≃ₐ[ℚ] ↥F₁) (x : AdeleRing (𝓞 ↥F) ↥F), J ((DD F).act (AlgEquiv.restrictNormalHom ↥F g') x) = (DD F₁).act g' (J x))
  (hJout : ∀ (T : Set (HeightOneSpectrum (𝓞 ℚ))) (z : (AdeleRing (𝓞 ↥F) ↥F)ˣ),
    (∀ w : HeightOneSpectrum (𝓞 ↥F), w.under (𝓞 ℚ) ∉ T → finPart w z = 1) →
    ∀ w' : HeightOneSpectrum (𝓞 ↥F₁), w'.under (𝓞 ℚ) ∉ T →
      finPart w' (Units.map (J : AdeleRing (𝓞 ↥F) ↥F →* AdeleRing (𝓞 ↥F₁) ↥F₁) z) = 1)
  (hJunit : ∀ (T : Set (HeightOneSpectrum (𝓞 ℚ))) (z : (AdeleRing (𝓞 ↥F) ↥F)ˣ),
    z ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 ↥F) ↥F {w | w.under (𝓞 ℚ) ∈ T} →
    Units.map (J : AdeleRing (𝓞 ↥F) ↥F →* AdeleRing (𝓞 ↥F₁) ↥F₁) z ∈
      NumberField.AdeleRing.unitIdelesOutside (𝓞 ↥F₁) ↥F₁ {w' | w'.under (𝓞 ℚ) ∈ T})
  (hJinf : ∀ z : (AdeleRing (𝓞 ↥F) ↥F)ˣ, infPart z = 1 → infPart (Units.map (J : AdeleRing (𝓞 ↥F) ↥F →* AdeleRing (𝓞 ↥F₁) ↥F₁) z) = 1)

noncomputable abbrev JJ : (AdeleRing (𝓞 ↥F) ↥F)ˣ →* (AdeleRing (𝓞 ↥F₁) ↥F₁)ˣ :=
  Units.map (J : AdeleRing (𝓞 ↥F) ↥F →* AdeleRing (𝓞 ↥F₁) ↥F₁)

include hJout in
theorem JJ_out : ∀ z : (AdeleRing (𝓞 ↥F) ↥F)ˣ, (∀ w : HeightOneSpectrum (𝓞 ↥F), w.under (𝓞 ℚ) ∉ Sq S → finPart w z = 1) →
    ∀ w' : HeightOneSpectrum (𝓞 ↥F₁), w'.under (𝓞 ℚ) ∉ Sq S → finPart w' (JJ F F₁ J z) = 1 :=
  fun z hz w' hw' => hJout (↑(Sq S)) z (fun w hw => hz w (by simpa using hw)) w' (by simpa using hw')

include hJeq in
theorem JJ_eq (g' : ↥F₁ ≃ₐ[ℚ] ↥F₁) (z : (AdeleRing (𝓞 ↥F) ↥F)ˣ) :
    JJ F F₁ J ((DD F).unitsAct (AlgEquiv.restrictNormalHom ↥F g') z) = (DD F₁).unitsAct g' (JJ F F₁ J z) :=
  Units.ext (hJeq g' (z : AdeleRing (𝓞 ↥F) ↥F))

def TOWER_J := NumberField.SArchIdele.existsUnique_hom_res_obj_comp_toSIdele_eq ℚ ↥F ↥F₁ (Sq S)
  (PhiF S F) (PhiF_inj S F) (PhiF_range S F) (PhiF_S S F) (PhiF_out S F) (PhiF_inf S F) (DD F) (PhiF_eq S F)
  (PhiF S F₁) (PhiF_inj S F₁) (PhiF_range S F₁) (PhiF_S S F₁) (PhiF_out S F₁) (PhiF_inf S F₁) (DD F₁) (PhiF_eq S F₁)
  (JJ F F₁ J) (JJ_out S F F₁ J hJout) (JJ_eq F F₁ J hJeq)

noncomputable def jJ : Rep.res (levelMapR F F₁ hle.out) (NumberField.SArchIdele.obj ℚ ↥F (Sq S)) ⟶ NumberField.SArchIdele.obj ℚ ↥F₁ (Sq S) :=
  (TOWER_J S F F₁ J hJeq hJout).choose

include hJeq hJout in
theorem jJ_spec (y : NumberField.SArchIdele.obj ℚ ↥F (Sq S)) :
    PhiF S F₁ ((NumberField.SArchIdele.toSIdele ℚ ↥F₁ (Sq S)).hom ((jJ S F F₁ J hJeq hJout).hom y)) =
      Additive.ofMul (JJ F F₁ J (Additive.toMul (PhiF S F ((NumberField.SArchIdele.toSIdele ℚ ↥F (Sq S)).hom y)))) :=
  (TOWER_J S F F₁ J hJeq hJout).choose_spec.1 y

end tower
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

end Reduce95
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

namespace Reduce95
open ExtCitation groupCohomology M4aHerbrand
open scoped NumberField.PlaceDecomp

section towerC

variable (S : Finset Nat.Primes) (F F₁ : IntermediateField ℚ (AlgebraicClosure ℚ))
  [NumberField ↥F] [IsGalois ℚ ↥F] [NumberField ↥F₁] [IsGalois ℚ ↥F₁] [hle : Fact (F ≤ F₁)]
  (J : AdeleRing (𝓞 ↥F) ↥F →+* AdeleRing (𝓞 ↥F₁) ↥F₁)
  (hJF : ∀ a : ↥F, J (algebraMap ↥F (AdeleRing (𝓞 ↥F) ↥F) a) = algebraMap ↥F₁ (AdeleRing (𝓞 ↥F₁) ↥F₁) (algebraMap ↥F ↥F₁ a))
  (hJeq : ∀ (g' : ↥F₁ ≃ₐ[ℚ] ↥F₁) (x : AdeleRing (𝓞 ↥F) ↥F), J ((DD F).act (AlgEquiv.restrictNormalHom ↥F g') x) = (DD F₁).act g' (J x))
  (hJout : ∀ (T : Set (HeightOneSpectrum (𝓞 ℚ))) (z : (AdeleRing (𝓞 ↥F) ↥F)ˣ),
    (∀ w : HeightOneSpectrum (𝓞 ↥F), w.under (𝓞 ℚ) ∉ T → finPart w z = 1) →
    ∀ w' : HeightOneSpectrum (𝓞 ↥F₁), w'.under (𝓞 ℚ) ∉ T →
      finPart w' (Units.map (J : AdeleRing (𝓞 ↥F) ↥F →* AdeleRing (𝓞 ↥F₁) ↥F₁) z) = 1)
  (hJunit : ∀ (T : Set (HeightOneSpectrum (𝓞 ℚ))) (z : (AdeleRing (𝓞 ↥F) ↥F)ˣ),
    z ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 ↥F) ↥F {w | w.under (𝓞 ℚ) ∈ T} →
    Units.map (J : AdeleRing (𝓞 ↥F) ↥F →* AdeleRing (𝓞 ↥F₁) ↥F₁) z ∈
      NumberField.AdeleRing.unitIdelesOutside (𝓞 ↥F₁) ↥F₁ {w' | w'.under (𝓞 ℚ) ∈ T})
  (hJinf : ∀ z : (AdeleRing (𝓞 ↥F) ↥F)ˣ, infPart z = 1 → infPart (Units.map (J : AdeleRing (𝓞 ↥F) ↥F →* AdeleRing (𝓞 ↥F₁) ↥F₁) z) = 1)

include hJF in
theorem JJ_principal : principalIdeles (𝓞 ↥F) ↥F ≤ (principalIdeles (𝓞 ↥F₁) ↥F₁).comap (JJ F F₁ J) := by
  rintro z ⟨a, rfl⟩
  refine ⟨Units.map (algebraMap ↥F ↥F₁ : ↥F →* ↥F₁) a, Units.ext ?_⟩
  change algebraMap ↥F₁ (AdeleRing (𝓞 ↥F₁) ↥F₁) (algebraMap ↥F ↥F₁ (a : ↥F)) = J (algebraMap ↥F (AdeleRing (𝓞 ↥F) ↥F) (a : ↥F))
  rw [hJF]

theorem TT_eq : TT S F = {w : HeightOneSpectrum (𝓞 ↥F) | w.under (𝓞 ℚ) ∈ (↑(Sq S) : Set (HeightOneSpectrum (𝓞 ℚ)))} := by
  ext w
  change w ∈ NumberField.placesOverPrimes ↥F (↑S : Set Nat.Primes) ↔ w.under (𝓞 ℚ) ∈ (↑(Sq S) : Set (HeightOneSpectrum (𝓞 ℚ)))
  rw [← setOf_under_mem_Sq S ↥F, Finset.mem_coe]
  rfl

include hJout hJunit hJinf in
theorem JJ_unitIdelesTrivialOn : unitIdelesTrivialOn (𝓞 ↥F) ↥F (TT S F) ≤ (unitIdelesTrivialOn (𝓞 ↥F₁) ↥F₁ (TT S F₁)).comap (JJ F F₁ J) := by
  intro z hz
  rw [Subgroup.mem_comap]
  have hz1 := unitIdelesTrivialOn_le_unitIdelesOutside _ _ _ hz
  have hz2 := unitIdelesTrivialOn_le_idelesTrivialOn _ _ _ hz
  rw [mem_idelesTrivialOn_iff] at hz2
  change JJ F F₁ J z ∈ NumberField.AdeleRing.unitIdelesOutside _ _ _ ⊓ idelesTrivialOn _ _ _
  rw [Subgroup.mem_inf]
  refine ⟨?_, ?_⟩
  ·
    rw [TT_eq S F] at hz1
    have h := hJunit (↑(Sq S)) z hz1
    rw [TT_eq S F₁]
    exact h
  · rw [mem_idelesTrivialOn_iff]
    refine ⟨hJinf z hz2.1, fun w' hw' => ?_⟩

    refine hJout ((↑(Sq S) : Set (HeightOneSpectrum (𝓞 ℚ)))ᶜ) z (fun w hw => hz2.2 w ?_) w' ?_
    · rw [TT_eq S F]; simpa using hw
    · rw [TT_eq S F₁] at hw'; simpa using hw'

include hJF hJout hJunit hJinf in
theorem JJ_sClassKernel : sClassKernel (𝓞 ↥F) ↥F (TT S F) ≤ (sClassKernel (𝓞 ↥F₁) ↥F₁ (TT S F₁)).comap (JJ F F₁ J) :=
  sup_le ((JJ_principal F F₁ J hJF).trans (Subgroup.comap_mono (principalIdeles_le_sClassKernel _ _ _)))
    ((JJ_unitIdelesTrivialOn S F F₁ J hJout hJunit hJinf).trans (Subgroup.comap_mono (unitIdelesTrivialOn_le_sClassKernel _ _ _)))

noncomputable def sClassMapJ : SIdeleClassGroup (𝓞 ↥F) ↥F (TT S F) →* SIdeleClassGroup (𝓞 ↥F₁) ↥F₁ (TT S F₁) :=
  QuotientGroup.map _ _ (JJ F F₁ J) (JJ_sClassKernel S F F₁ J hJF hJout hJunit hJinf)

theorem sClassMapJ_mk (x : (AdeleRing (𝓞 ↥F) ↥F)ˣ) :
    sClassMapJ S F F₁ J hJF hJout hJunit hJinf (QuotientGroup.mk x) = QuotientGroup.mk (JJ F F₁ J x) := rfl

include hJeq in
theorem sClassMapJ_smul (g' : ↥F₁ ≃ₐ[ℚ] ↥F₁) (c : SIdeleClassGroup (𝓞 ↥F) ↥F (TT S F)) :
    sClassMapJ S F F₁ J hJF hJout hJunit hJinf ((levelMapR F F₁ hle.out g') • c) = g' • sClassMapJ S F F₁ J hJF hJout hJunit hJinf c := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c
  have h1 : (levelMapR F F₁ hle.out g') • (QuotientGroup.mk x : SIdeleClassGroup (𝓞 ↥F) ↥F (TT S F)) =
      QuotientGroup.mk ((DD F).unitsAct (AlgEquiv.restrictNormalHom ↥F g') x) := by
    rw [← toSIdeleClass_mk, hactS_F S F, IdeleGaloisDescent.classAct_mk, toSIdeleClass_mk]; rfl
  have h2 : g' • (QuotientGroup.mk (JJ F F₁ J x) : SIdeleClassGroup (𝓞 ↥F₁) ↥F₁ (TT S F₁)) =
      QuotientGroup.mk ((DD F₁).unitsAct g' (JJ F F₁ J x)) := by
    rw [← toSIdeleClass_mk, hactS_F S F₁, IdeleGaloisDescent.classAct_mk, toSIdeleClass_mk]
  rw [h1, sClassMapJ_mk, sClassMapJ_mk, h2, JJ_eq F F₁ J hJeq]

noncomputable def jC : Rep.res (levelMapR F F₁ hle.out) (CS S F) ⟶ CS S F₁ :=
  repHomResOfMulEquivariant (levelMapR F F₁ hle.out) (sClassMapJ S F F₁ J hJF hJout hJunit hJinf)
    (sClassMapJ_smul S F F₁ J hJF hJeq hJout hJunit hJinf)

theorem jC_hom_apply (c : Additive (SIdeleClassGroup (𝓞 ↥F) ↥F (TT S F))) :
    (jC S F F₁ J hJF hJeq hJout hJunit hJinf).hom c = Additive.ofMul (sClassMapJ S F F₁ J hJF hJout hJunit hJinf (Additive.toMul c)) := rfl

theorem hsqC : (Rep.resFunctor (levelMapR F F₁ hle.out)).map (LF S F) ≫ jC S F F₁ J hJF hJeq hJout hJunit hJinf =
    jJ S F F₁ J hJeq hJout ≫ LF S F₁ := by
  apply Rep.hom_ext
  apply DFunLike.ext
  intro y
  change (jC S F F₁ J hJF hJeq hJout hJunit hJinf).hom ((LF S F).hom y) = (LF S F₁).hom ((jJ S F F₁ J hJeq hJout).hom y)
  rw [jC_hom_apply]
  unfold LF
  rw [LS_hom_apply, LS_hom_apply, toMul_ofMul, jJ_spec S F F₁ J hJeq hJout, toMul_ofMul]
  rfl

end towerC
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

end Reduce95
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

namespace Reduce95
open ExtCitation groupCohomology M4aHerbrand
open scoped NumberField.PlaceDecomp

section towerE

variable (S : Finset Nat.Primes) (F F₁ : IntermediateField ℚ (AlgebraicClosure ℚ))
  [NumberField ↥F] [IsGalois ℚ ↥F] [NumberField ↥F₁] [IsGalois ℚ ↥F₁] [hle : Fact (F ≤ F₁)]
  (J : AdeleRing (𝓞 ↥F) ↥F →+* AdeleRing (𝓞 ↥F₁) ↥F₁)
  (hJF : ∀ a : ↥F, J (algebraMap ↥F (AdeleRing (𝓞 ↥F) ↥F) a) = algebraMap ↥F₁ (AdeleRing (𝓞 ↥F₁) ↥F₁) (algebraMap ↥F ↥F₁ a))
  (hJeq : ∀ (g' : ↥F₁ ≃ₐ[ℚ] ↥F₁) (x : AdeleRing (𝓞 ↥F) ↥F), J ((DD F).act (AlgEquiv.restrictNormalHom ↥F g') x) = (DD F₁).act g' (J x))
  (hJout : ∀ (T : Set (HeightOneSpectrum (𝓞 ℚ))) (z : (AdeleRing (𝓞 ↥F) ↥F)ˣ),
    (∀ w : HeightOneSpectrum (𝓞 ↥F), w.under (𝓞 ℚ) ∉ T → finPart w z = 1) →
    ∀ w' : HeightOneSpectrum (𝓞 ↥F₁), w'.under (𝓞 ℚ) ∉ T →
      finPart w' (Units.map (J : AdeleRing (𝓞 ↥F) ↥F →* AdeleRing (𝓞 ↥F₁) ↥F₁) z) = 1)
  (hJunit : ∀ (T : Set (HeightOneSpectrum (𝓞 ℚ))) (z : (AdeleRing (𝓞 ↥F) ↥F)ˣ),
    z ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 ↥F) ↥F {w | w.under (𝓞 ℚ) ∈ T} →
    Units.map (J : AdeleRing (𝓞 ↥F) ↥F →* AdeleRing (𝓞 ↥F₁) ↥F₁) z ∈
      NumberField.AdeleRing.unitIdelesOutside (𝓞 ↥F₁) ↥F₁ {w' | w'.under (𝓞 ℚ) ∈ T})
  (hJinf : ∀ z : (AdeleRing (𝓞 ↥F) ↥F)ˣ, infPart z = 1 → infPart (Units.map (J : AdeleRing (𝓞 ↥F) ↥F →* AdeleRing (𝓞 ↥F₁) ↥F₁) z) = 1)

local notation "πT" => levelMapR F F₁ (Fact.out : F ≤ F₁)
local notation "E_" K => NumberField.SUnits.sUnitsRep ℚ (↥K) (Sq S)
local notation "dg" K => NumberField.SArchIdele.diagS ℚ (↥K) (Sq S)

include hJF hJeq hJout hJunit hJinf in

theorem LF_jJ_diagS (e : E_ F) : (LF S F₁).hom ((jJ S F F₁ J hJeq hJout).hom ((dg F).hom e)) = 0 := by
  have h := congrArg (fun φ => φ.hom ((dg F).hom e)) (hsqC S F F₁ J hJF hJeq hJout hJunit hJinf)
  change (jC S F F₁ J hJF hJeq hJout hJunit hJinf).hom ((LF S F).hom ((dg F).hom e)) =
    (LF S F₁).hom ((jJ S F F₁ J hJeq hJout).hom ((dg F).hom e)) at h
  rw [hL1F S F e, map_zero] at h
  exact h.symm

noncomputable def jEfun (e : E_ F) : E_ F₁ :=
  (hL2F S F₁ _ (LF_jJ_diagS S F F₁ J hJF hJeq hJout hJunit hJinf e)).choose

theorem diagS_jEfun (e : E_ F) :
    (dg F₁).hom (jEfun S F F₁ J hJF hJeq hJout hJunit hJinf e) = (jJ S F F₁ J hJeq hJout).hom ((dg F).hom e) :=
  (hL2F S F₁ _ (LF_jJ_diagS S F F₁ J hJF hJeq hJout hJunit hJinf e)).choose_spec

noncomputable def jElin : (E_ F) →ₗ[ℤ] (E_ F₁) :=
  LinearMap.mk
    ⟨jEfun S F F₁ J hJF hJeq hJout hJunit hJinf, fun x y => diagS_injective ↥F₁ (Sq S) (by
      have h1 := (dg F₁).hom.toLinearMap.map_add (jEfun S F F₁ J hJF hJeq hJout hJunit hJinf x) (jEfun S F F₁ J hJF hJeq hJout hJunit hJinf y)
      have h2 := (dg F).hom.toLinearMap.map_add x y
      have h3 := (jJ S F F₁ J hJeq hJout).hom.toLinearMap.map_add ((dg F).hom x) ((dg F).hom y)
      rw [Representation.IntertwiningMap.coe_toLinearMap] at h1 h2 h3
      rw [diagS_jEfun, h1, diagS_jEfun, diagS_jEfun, h2, h3])⟩
    (fun n x => diagS_injective ↥F₁ (Sq S) (by
      dsimp only [RingHom.id_apply]
      have h1 := (dg F₁).hom.toLinearMap.map_smul n (jEfun S F F₁ J hJF hJeq hJout hJunit hJinf x)
      have h2 := (dg F).hom.toLinearMap.map_smul n x
      have h3 := (jJ S F F₁ J hJeq hJout).hom.toLinearMap.map_smul n ((dg F).hom x)
      rw [Representation.IntertwiningMap.coe_toLinearMap] at h1 h2 h3
      rw [h1, diagS_jEfun, diagS_jEfun, h2, h3]))

theorem jElin_apply (e : E_ F) : jElin S F F₁ J hJF hJeq hJout hJunit hJinf e = jEfun S F F₁ J hJF hJeq hJout hJunit hJinf e := rfl

noncomputable def jE : Rep.res πT (E_ F) ⟶ E_ F₁ :=
  Rep.ofHom ⟨jElin S F F₁ J hJF hJeq hJout hJunit hJinf, fun g => LinearMap.ext fun e => diagS_injective ↥F₁ (Sq S) (by
    change (dg F₁).hom (jEfun S F F₁ J hJF hJeq hJout hJunit hJinf ((E_ F).ρ (πT g) e)) =
      (dg F₁).hom ((E_ F₁).ρ g (jEfun S F F₁ J hJF hJeq hJout hJunit hJinf e))
    rw [diagS_jEfun, Rep.hom_comm_apply, Rep.hom_comm_apply, diagS_jEfun]
    exact Rep.hom_comm_apply (jJ S F F₁ J hJeq hJout) g ((dg F).hom e))⟩

theorem jE_hom_apply (e : E_ F) : (jE S F F₁ J hJF hJeq hJout hJunit hJinf).hom e = jEfun S F F₁ J hJF hJeq hJout hJunit hJinf e := rfl

theorem hsqE : (Rep.resFunctor πT).map (seqF S F).f ≫ jJ S F F₁ J hJeq hJout = jE S F F₁ J hJF hJeq hJout hJunit hJinf ≫ (seqF S F₁).f := by
  apply Rep.hom_ext; apply DFunLike.ext; intro e
  change (jJ S F F₁ J hJeq hJout).hom ((dg F).hom e) = (dg F₁).hom ((jE S F F₁ J hJF hJeq hJout hJunit hJinf).hom e)
  rw [jE_hom_apply, diagS_jEfun]

end towerE
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

end Reduce95
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

namespace Reduce95
open ExtCitation groupCohomology GroupCohomology M4aHerbrand
open scoped NumberField.PlaceDecomp

section towerY

variable (S : Finset Nat.Primes) (F F₁ : IntermediateField ℚ (AlgebraicClosure ℚ))
  [NumberField ↥F] [IsGalois ℚ ↥F] [NumberField ↥F₁] [IsGalois ℚ ↥F₁] [hle : Fact (F ≤ F₁)]
  (J : AdeleRing (𝓞 ↥F) ↥F →+* AdeleRing (𝓞 ↥F₁) ↥F₁)
  (hJF : ∀ a : ↥F, J (algebraMap ↥F (AdeleRing (𝓞 ↥F) ↥F) a) = algebraMap ↥F₁ (AdeleRing (𝓞 ↥F₁) ↥F₁) (algebraMap ↥F ↥F₁ a))
  (hJeq : ∀ (g' : ↥F₁ ≃ₐ[ℚ] ↥F₁) (x : AdeleRing (𝓞 ↥F) ↥F), J ((DD F).act (AlgEquiv.restrictNormalHom ↥F g') x) = (DD F₁).act g' (J x))
  (hJout : ∀ (T : Set (HeightOneSpectrum (𝓞 ℚ))) (z : (AdeleRing (𝓞 ↥F) ↥F)ˣ),
    (∀ w : HeightOneSpectrum (𝓞 ↥F), w.under (𝓞 ℚ) ∉ T → finPart w z = 1) →
    ∀ w' : HeightOneSpectrum (𝓞 ↥F₁), w'.under (𝓞 ℚ) ∉ T →
      finPart w' (Units.map (J : AdeleRing (𝓞 ↥F) ↥F →* AdeleRing (𝓞 ↥F₁) ↥F₁) z) = 1)
  (hJunit : ∀ (T : Set (HeightOneSpectrum (𝓞 ℚ))) (z : (AdeleRing (𝓞 ↥F) ↥F)ˣ),
    z ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 ↥F) ↥F {w | w.under (𝓞 ℚ) ∈ T} →
    Units.map (J : AdeleRing (𝓞 ↥F) ↥F →* AdeleRing (𝓞 ↥F₁) ↥F₁) z ∈
      NumberField.AdeleRing.unitIdelesOutside (𝓞 ↥F₁) ↥F₁ {w' | w'.under (𝓞 ℚ) ∈ T})
  (hJinf : ∀ z : (AdeleRing (𝓞 ↥F) ↥F)ˣ, infPart z = 1 → infPart (Units.map (J : AdeleRing (𝓞 ↥F) ↥F →* AdeleRing (𝓞 ↥F₁) ↥F₁) z) = 1)

noncomputable def jY : Rep.res (levelMapR F F₁ hle.out) (seqF S F).X₃ ⟶ (seqF S F₁).X₃ :=
  RepImage.map ((Rep.resFunctor (levelMapR F F₁ hle.out)).map (LF S F)) (LF S F₁) (jJ S F F₁ J hJeq hJout) (jC S F F₁ J hJF hJeq hJout hJunit hJinf)
    (hsqC S F F₁ J hJF hJeq hJout hJunit hJinf)

theorem ι_jY (y : (seqF S F).X₃) :
    (RepImage.ι (LF S F₁)).hom ((jY S F F₁ J hJF hJeq hJout hJunit hJinf).hom y) =
      (jC S F F₁ J hJF hJeq hJout hJunit hJinf).hom ((RepImage.ι (LF S F)).hom y) := rfl

theorem hsqCι : (Rep.resFunctor (levelMapR F F₁ hle.out)).map (RepImage.ι (LF S F)) ≫ jC S F F₁ J hJF hJeq hJout hJunit hJinf =
    jY S F F₁ J hJF hJeq hJout hJunit hJinf ≫ RepImage.ι (LF S F₁) :=
  (RepImage.map_ι ((Rep.resFunctor (levelMapR F F₁ hle.out)).map (LF S F)) (LF S F₁) (jJ S F F₁ J hJeq hJout) (jC S F F₁ J hJF hJeq hJout hJunit hJinf)
    (hsqC S F F₁ J hJF hJeq hJout hJunit hJinf)).symm

theorem hsqY : (Rep.resFunctor (levelMapR F F₁ hle.out)).map (seqF S F).g ≫ jY S F F₁ J hJF hJeq hJout hJunit hJinf =
    jJ S F F₁ J hJeq hJout ≫ (seqF S F₁).g := by
  apply Rep.hom_ext; apply DFunLike.ext; intro y
  apply RepImage.ι_hom_injective (LF S F₁)
  change (RepImage.ι (LF S F₁)).hom ((jY S F F₁ J hJF hJeq hJout hJunit hJinf).hom ((RepImage.toImage (LF S F)).hom y)) =
    (RepImage.ι (LF S F₁)).hom ((RepImage.toImage (LF S F₁)).hom ((jJ S F F₁ J hJeq hJout).hom y))
  rw [ι_jY]
  change (jC S F F₁ J hJF hJeq hJout hJunit hJinf).hom ((LF S F).hom y) = (LF S F₁).hom ((jJ S F F₁ J hJeq hJout).hom y)
  exact congrArg (fun φ => φ.hom y) (hsqC S F F₁ J hJF hJeq hJout hJunit hJinf)

variable
  (j : Rep.res (levelMapR F F₁ hle.out) (Rep.ofMulDistribMulAction (↥F ≃ₐ[ℚ] ↥F) (IdeleClassGroup (𝓞 ↥F) ↥F)) ⟶
    Rep.ofMulDistribMulAction (↥F₁ ≃ₐ[ℚ] ↥F₁) (IdeleClassGroup (𝓞 ↥F₁) ↥F₁))
  (hj : ∀ x : (AdeleRing (𝓞 ↥F) ↥F)ˣ, j.hom (Additive.ofMul (QuotientGroup.mk x : IdeleClassGroup (𝓞 ↥F) ↥F)) =
    Additive.ofMul (QuotientGroup.mk (JJ F F₁ J x) : IdeleClassGroup (𝓞 ↥F₁) ↥F₁))
  (invGF' : ↥(groupCohomology (Rep.ofMulDistribMulAction (↥F ≃ₐ[ℚ] ↥F) (IdeleClassGroup (𝓞 ↥F) ↥F)) 2) →+ AddCircle (1 : ℚ))
  (invGF₁' : ↥(groupCohomology (Rep.ofMulDistribMulAction (↥F₁ ≃ₐ[ℚ] ↥F₁) (IdeleClassGroup (𝓞 ↥F₁) ↥F₁)) 2) →+ AddCircle (1 : ℚ))
  (hvii : ∀ x, invGF₁' ((groupCohomology.map (levelMapR F F₁ hle.out) j 2).hom x) = invGF' x)

include hj in

theorem hsq_qSF : (Rep.resFunctor (levelMapR F F₁ hle.out)).map (qSF S F) ≫ jC S F F₁ J hJF hJeq hJout hJunit hJinf = j ≫ qSF S F₁ := by
  apply Rep.hom_ext; apply DFunLike.ext; intro c
  obtain ⟨c, rfl⟩ : ∃ d, Additive.ofMul d = c := ⟨Additive.toMul c, rfl⟩
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c
  change (jC S F F₁ J hJF hJeq hJout hJunit hJinf).hom ((qSF S F).hom (Additive.ofMul (QuotientGroup.mk x))) =
    (qSF S F₁).hom (j.hom (Additive.ofMul (QuotientGroup.mk x)))
  rw [hj]
  rfl

end towerY
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

end Reduce95
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

namespace Reduce95
open ExtCitation groupCohomology GroupCohomology M4aHerbrand

structure InvSys (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] where
  invG : ↥(groupCohomology (Rep.ofMulDistribMulAction (↥F ≃ₐ[ℚ] ↥F) (IdeleClassGroup (𝓞 ↥F) ↥F)) 2) →+ AddCircle (1 : ℚ)
  inv : ∀ H : Subgroup (↥F ≃ₐ[ℚ] ↥F),
    ↥(groupCohomology (Rep.res H.subtype (Rep.ofMulDistribMulAction (↥F ≃ₐ[ℚ] ↥F) (IdeleClassGroup (𝓞 ↥F) ↥F))) 2) →+ AddCircle (1 : ℚ)
  hinjG : Function.Injective invG
  hinj : ∀ H, Function.Injective (inv H)
  hrangeG : ∀ t : AddCircle (1 : ℚ), t ∈ invG.range ↔ Nat.card (↥F ≃ₐ[ℚ] ↥F) • t = 0
  hrange : ∀ (H : Subgroup (↥F ≃ₐ[ℚ] ↥F)) (t : AddCircle (1 : ℚ)), t ∈ (inv H).range ↔ Nat.card ↥H • t = 0
  hii : ∀ (H : Subgroup (↥F ≃ₐ[ℚ] ↥F)) (x : ↥(groupCohomology (Rep.ofMulDistribMulAction (↥F ≃ₐ[ℚ] ↥F) (IdeleClassGroup (𝓞 ↥F) ↥F)) 2)),
    inv H ((groupCohomology.map H.subtype (𝟙 (Rep.res H.subtype (Rep.ofMulDistribMulAction (↥F ≃ₐ[ℚ] ↥F) (IdeleClassGroup (𝓞 ↥F) ↥F)))) 2).hom x) = H.index • invG x
  hv : ∀ (H : Subgroup (↥F ≃ₐ[ℚ] ↥F))
    (cor : ↥(groupCohomology (Rep.res H.subtype (Rep.ofMulDistribMulAction (↥F ≃ₐ[ℚ] ↥F) (IdeleClassGroup (𝓞 ↥F) ↥F))) 2) →+
      ↥(groupCohomology (Rep.ofMulDistribMulAction (↥F ≃ₐ[ℚ] ↥F) (IdeleClassGroup (𝓞 ↥F) ↥F)) 2)),
    (∀ x, cor ((groupCohomology.map H.subtype (𝟙 (Rep.res H.subtype (Rep.ofMulDistribMulAction (↥F ≃ₐ[ℚ] ↥F) (IdeleClassGroup (𝓞 ↥F) ↥F)))) 2).hom x) = H.index • x) →
    ∀ y, invG (cor y) = inv H y

section invSys

variable {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes)
  (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F]
  (hunr : ∀ w : HeightOneSpectrum (𝓞 ↥F), w ∉ TT S F → Ideal.ramificationIdx' (w.asIdeal.under (𝓞 ℚ)) w.asIdeal = 1)
  (sys : InvSys F)

noncomputable abbrev invGSFs := invG' (qSF S F) (qSF_bijective S F hunr) sys.invG sys.inv sys.hinj sys.hrangeG sys.hrange sys.hii
noncomputable abbrev invSFs (H : Subgroup (↥F ≃ₐ[ℚ] ↥F)) := inv' (qSF S F) (qSF_bijective S F hunr) sys.inv H

include hunr in
theorem invGSFs_injective : Function.Injective (invGSFs S F hunr sys) :=
  invG'_injective (qSF S F) (qSF_bijective S F hunr) sys.invG sys.inv sys.hinjG sys.hinj sys.hrangeG sys.hrange sys.hii

include hunr in
theorem invGSFs_range : ∀ t : AddCircle (1 : ℚ), t ∈ (invGSFs S F hunr sys).range ↔ Nat.card (↥F ≃ₐ[ℚ] ↥F) • t = 0 :=
  invG'_range (qSF S F) (qSF_bijective S F hunr) sys.invG sys.inv sys.hinj sys.hrangeG sys.hrange sys.hii

include hunr in
theorem invSFs_injective (H : Subgroup (↥F ≃ₐ[ℚ] ↥F)) : Function.Injective (invSFs S F hunr sys H) :=
  inv'_injective (qSF S F) (qSF_bijective S F hunr) sys.inv sys.hinj H

include hunr in
theorem invSFs_apply (H : Subgroup (↥F ≃ₐ[ℚ] ↥F)) (x) :
    invSFs S F hunr sys H ((groupCohomology.map (MonoidHom.id ↥H) ((Rep.resFunctor H.subtype).map (qSF S F)) 2).hom x) = sys.inv H x :=
  inv'_apply (qSF S F) (qSF_bijective S F hunr) sys.inv H x

include hunr in
theorem invGSFs_apply (x) : invGSFs S F hunr sys ((groupCohomology.map (MonoidHom.id _) (qSF S F) 2).hom x) = sys.invG x :=
  invG'_apply (qSF S F) (qSF_bijective S F hunr) sys.invG sys.inv sys.hinj sys.hrangeG sys.hrange sys.hii x

include hunr in

theorem hcor_s (v : extArithIndex S) (cor : ↥(groupCohomology (Rep.res (Dv S F v).subtype (CS S F)) 2) →+ ↥(groupCohomology (CS S F) 2))
    (hcor : ∀ x : ↥(groupCohomology (CS S F) 2),
      cor ((groupCohomology.map (Dv S F v).subtype (𝟙 (Rep.res (Dv S F v).subtype (CS S F))) 2).hom x) = (Dv S F v).index • x)
    (y : ↥(groupCohomology (Rep.res (Dv S F v).subtype (CS S F)) 2)) :
    invGSFs S F hunr sys (cor y) = invSFs S F hunr sys (Dv S F v) y :=
  invG'_cor (qSF S F) (qSF_bijective S F hunr) sys.invG sys.inv sys.hinj sys.hrangeG sys.hrange sys.hii sys.hv (Dv S F v) cor hcor y

variable (B : Rep ℤ (↥F ≃ₐ[ℚ] ↥F)) [Fintype B] (hB : ∀ b : B, p • b = 0)

include hunr hB in
theorem exists_alFs : ∃ al : (Rep.relationModuleInt B ⟶ CS S F) →+ (↥(groupCohomology B 1) →+ ZMod p),
      ∀ (φ : Rep.relationModuleInt B ⟶ CS S F) (y : ↥(groupCohomology B 1)),
        invGSFs S F hunr sys ((groupCohomology.map (MonoidHom.id _) φ 2).hom ((groupCohomology.δ (hX' F B) 1 2 rfl).hom y))
            = ((((al φ y).val : ℚ) / (p : ℚ) : ℚ) : AddCircle (1 : ℚ)) ∧
        (al φ y = 0 ↔ (groupCohomology.map (MonoidHom.id _) φ 2).hom ((groupCohomology.δ (hX' F B) 1 2 rfl).hom y) = 0) :=
  groupCohomology.exists_alpha1Read_of_injective_invariant (CS S F) (invGSFs S F hunr sys) (invGSFs_injective S F hunr sys) p B hB (hX' F B)

noncomputable def alFs : (Rep.relationModuleInt B ⟶ CS S F) →+ (↥(groupCohomology B 1) →+ ZMod p) :=
  (exists_alFs S F hunr sys B hB).choose

include hunr hB in
theorem alFs_hal (φ : Rep.relationModuleInt B ⟶ CS S F) (y : ↥(groupCohomology B 1)) :
    invGSFs S F hunr sys ((groupCohomology.map (MonoidHom.id _) φ 2).hom ((groupCohomology.δ (hX' F B) 1 2 rfl).hom y))
      = ((((alFs S F hunr sys B hB φ y).val : ℚ) / (p : ℚ) : ℚ) : AddCircle (1 : ℚ)) :=
  ((exists_alFs S F hunr sys B hB).choose_spec φ y).1

include hunr hB in
theorem alFs_eq_zero_iff (φ : Rep.relationModuleInt B ⟶ CS S F) (y : ↥(groupCohomology B 1)) :
    alFs S F hunr sys B hB φ y = 0 ↔ (groupCohomology.map (MonoidHom.id _) φ 2).hom ((groupCohomology.δ (hX' F B) 1 2 rfl).hom y) = 0 :=
  ((exists_alFs S F hunr sys B hB).choose_spec φ y).2

include hunr hB in

theorem alFs_surjective (hpG : p ∣ Nat.card (↥F ≃ₐ[ℚ] ↥F)) (g : ↥(groupCohomology B 1) →+ ZMod p) :
    ∃ φ : Rep.relationModuleInt B ⟶ CS S F, alFs S F hunr sys B hB φ = g :=
  al_surjective p (CS S F) (invGSFs S F hunr sys) (invGSFs_injective S F hunr sys) (invGSFs_range S F hunr sys) hpG B (hX' F B)
    (alFs S F hunr sys B hB) (alFs_hal S F hunr sys B hB) (hSURJ_F S F hunr B) g

set_option maxHeartbeats 3200000 in
include hunr hB in

theorem alFs_ι_comp (χ : Rep.free ℤ (↥F ≃ₐ[ℚ] ↥F) B ⟶ CS S F) : alFs S F hunr sys B hB (Rep.relationModuleInt.ι B ≫ χ) = 0 := by
  ext y
  rw [AddMonoidHom.zero_apply, alFs_eq_zero_iff]
  have hc := groupCohomology.map_id_comp (Rep.relationModuleInt.ι B) χ 2
  have hc' := congrArg (fun φ => (ModuleCat.Hom.hom φ) ((groupCohomology.δ (hX' F B) 1 2 rfl).hom y)) hc
  refine hc'.trans ?_
  change (groupCohomology.map (MonoidHom.id (↥F ≃ₐ[ℚ] ↥F)) χ 2).hom
    ((groupCohomology.map (MonoidHom.id (↥F ≃ₐ[ℚ] ↥F)) (Rep.relationModuleInt.ι B) 2).hom ((groupCohomology.δ (hX' F B) 1 2 rfl).hom y)) = 0
  have h0 := map_f_delta_eq_zero (hX' F B) 1 2 rfl y
  have h1 : (groupCohomology.map (MonoidHom.id (↥F ≃ₐ[ℚ] ↥F)) (Rep.relationModuleInt.ι B) 2).hom ((groupCohomology.δ (hX' F B) 1 2 rfl).hom y) = 0 := h0
  rw [h1, map_zero]

end invSys
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

section hIDs
open scoped Classical

variable {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes)
  (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) [FiniteDimensional (ZMod p) M]
  (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p)
  (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F] [IsTotallyComplex ↥F]
  (hζF : ζ ∈ F)
  (hunr : ∀ w : HeightOneSpectrum (𝓞 ↥F), w ∉ TT S F → Ideal.ramificationIdx' (w.asIdeal.under (𝓞 ℚ)) w.asIdeal = 1)
  (sys : InvSys F)
  (B : Rep ℤ (↥F ≃ₐ[ℚ] ↥F)) [Fintype B] (β : B →+ M.dualTwist (cycloChar p))
  (hβeq : ∀ (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (b : B),
    β (B.ρ (AlgEquiv.restrictNormalHom ↥F γ) b) = (M.dualTwist (cycloChar p)).ρ γ (β b))
  (hβ : Function.Bijective β) (hB : ∀ b : B, p • b = 0)
  (θ : ∀ v : extArithIndex S,
    continuousH1 (extArithLoc S v) (Rep.res (extArithLoc S v) M) →ₗ[ZMod p]
      Module.Dual (ZMod p) (continuousH1 (extArithLoc S v) (Rep.res (extArithLoc S v) (M.dualTwist (cycloChar p)))))
  (hloc : ∀ y ∈ continuousH1S S (M.dualTwist (cycloChar p)), ∀ v : extArithIndex S,
    locTotal (extArithLoc S) (M.dualTwist (cycloChar p)) y v ∈ continuousH1 (extArithLoc S v) (Rep.res (extArithLoc S v) (M.dualTwist (cycloChar p))))
  (infl : ↥(groupCohomology B 1) →+ H1 (M.dualTwist (cycloChar p)))
  (u : extArithIndex S → (ZMod p)ˣ)
  (hLOC : ∀ (v : extArithIndex S) (sv : Rep.res (Dv S F v).subtype (Rep.relationModuleInt B) ⟶ Yv S F v)
      (x : ↥(groupCohomology B 1)) (hx : infl x ∈ continuousH1S S (M.dualTwist (cycloChar p))),
    invSFs S F hunr sys (Dv S F v) ((groupCohomology.map (MonoidHom.id ↥(Dv S F v)) (sv ≫ lamV S F (LF S F) v) 2).hom
      ((groupCohomology.δ (hXv' S F B v) 1 2 rfl).hom
        ((groupCohomology.map (Dv S F v).subtype (𝟙 (Rep.res (Dv S F v).subtype B)) 1).hom x)))
      = (((((u v : ZMod p) * θ v (LamV S M ζ hζ F hζF B β hβeq hβ hB v sv)
          ⟨locTotal (extArithLoc S) (M.dualTwist (cycloChar p)) (infl x) v, hloc _ hx v⟩).val : ℚ) / (p : ℚ) : ℚ) : AddCircle (1 : ℚ)))

include hLOC in

theorem hIDs (s : Rep.relationModuleInt B ⟶ NumberField.SArchIdele.obj ℚ ↥F (Sq S)) (x : ↥(groupCohomology B 1))
    (hx : infl x ∈ continuousH1S S (M.dualTwist (cycloChar p))) :
    alFs S F hunr sys B hB (s ≫ (seqF S F).g ≫ RepImage.ι (LF S F)) x =
      ∑ v, (u v : ZMod p) * θ v (LJ1 S M ζ hζ F hζF B β hβeq hβ hB s v)
        ⟨locTotal (extArithLoc S) (M.dualTwist (cycloChar p)) (infl x) v, hloc _ hx v⟩ := by
  have hfac : s ≫ (seqF S F).g ≫ RepImage.ι (LF S F) = (s ≫ rHom S F) ≫ lamJ0 S F (LF S F) := by
    rw [Category.assoc, rHom_lamJ0]
    exact congrArg (s ≫ ·) (RepImage.toImage_ι (LF S F))
  rw [hfac]
  exact groupCohomology.alpha1Read_comp_eq_sum_theta_of_forall_local S M θ hloc (Dv S F) (Yv S F) (CS S F)
    (lamV S F (LF S F)) (lamJ0 S F (LF S F)) rfl B hB (hX' F B) (hXv' S F B)
    (invGSFs S F hunr sys) (fun v => invSFs S F hunr sys (Dv S F v)) (hcor_s S F hunr sys)
    (alFs S F hunr sys B hB) (alFs_hal S F hunr sys B hB) infl (LamV S M ζ hζ F hζF B β hβeq hβ hB) u hLOC (s ≫ rHom S F) x hx

variable {VB₀ : Type} [AddCommGroup VB₀] (infl₀ : VB₀ →+ H1 (M.dualTwist (cycloChar p))) (ι : VB₀ →+ ↥(groupCohomology B 1))
  (hcomp : ∀ x, infl (ι x) = infl₀ x)

include hLOC hcomp in

theorem hIDs' (s : Rep.relationModuleInt B ⟶ NumberField.SArchIdele.obj ℚ ↥F (Sq S)) (x : VB₀)
    (hx : infl₀ x ∈ continuousH1S S (M.dualTwist (cycloChar p))) :
    alFs S F hunr sys B hB (s ≫ (seqF S F).g ≫ RepImage.ι (LF S F)) (ι x) =
      ∑ v, (u v : ZMod p) * θ v (LJ1 S M ζ hζ F hζF B β hβeq hβ hB s v)
        ⟨locTotal (extArithLoc S) (M.dualTwist (cycloChar p)) (infl₀ x) v, hloc _ hx v⟩ := by
  have hx' : infl (ι x) ∈ continuousH1S S (M.dualTwist (cycloChar p)) := by rw [hcomp]; exact hx
  rw [hIDs S M ζ hζ F hζF hunr sys B β hβeq hβ hB θ hloc infl u hLOC s (ι x) hx']
  refine Finset.sum_congr rfl fun v _ => ?_
  congr 2
  apply Subtype.ext
  simp only [hcomp]

end hIDs
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

end Reduce95
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

namespace Reduce95
open ExtCitation groupCohomology GroupCohomology M4aHerbrand

section towerInv

variable (S : Finset Nat.Primes) (F F₁ : IntermediateField ℚ (AlgebraicClosure ℚ))
  [NumberField ↥F] [IsGalois ℚ ↥F] [NumberField ↥F₁] [IsGalois ℚ ↥F₁] [hle : Fact (F ≤ F₁)]
  (hunr : ∀ w : HeightOneSpectrum (𝓞 ↥F), w ∉ TT S F → Ideal.ramificationIdx' (w.asIdeal.under (𝓞 ℚ)) w.asIdeal = 1)
  (hunr₁ : ∀ w : HeightOneSpectrum (𝓞 ↥F₁), w ∉ TT S F₁ → Ideal.ramificationIdx' (w.asIdeal.under (𝓞 ℚ)) w.asIdeal = 1)
  (sys : InvSys F) (sys₁ : InvSys F₁)
  (J : AdeleRing (𝓞 ↥F) ↥F →+* AdeleRing (𝓞 ↥F₁) ↥F₁)
  (hJF : ∀ a : ↥F, J (algebraMap ↥F (AdeleRing (𝓞 ↥F) ↥F) a) = algebraMap ↥F₁ (AdeleRing (𝓞 ↥F₁) ↥F₁) (algebraMap ↥F ↥F₁ a))
  (hJeq : ∀ (g' : ↥F₁ ≃ₐ[ℚ] ↥F₁) (x : AdeleRing (𝓞 ↥F) ↥F), J ((DD F).act (AlgEquiv.restrictNormalHom ↥F g') x) = (DD F₁).act g' (J x))
  (hJout : ∀ (T : Set (HeightOneSpectrum (𝓞 ℚ))) (z : (AdeleRing (𝓞 ↥F) ↥F)ˣ),
    (∀ w : HeightOneSpectrum (𝓞 ↥F), w.under (𝓞 ℚ) ∉ T → finPart w z = 1) →
    ∀ w' : HeightOneSpectrum (𝓞 ↥F₁), w'.under (𝓞 ℚ) ∉ T →
      finPart w' (Units.map (J : AdeleRing (𝓞 ↥F) ↥F →* AdeleRing (𝓞 ↥F₁) ↥F₁) z) = 1)
  (hJunit : ∀ (T : Set (HeightOneSpectrum (𝓞 ℚ))) (z : (AdeleRing (𝓞 ↥F) ↥F)ˣ),
    z ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 ↥F) ↥F {w | w.under (𝓞 ℚ) ∈ T} →
    Units.map (J : AdeleRing (𝓞 ↥F) ↥F →* AdeleRing (𝓞 ↥F₁) ↥F₁) z ∈
      NumberField.AdeleRing.unitIdelesOutside (𝓞 ↥F₁) ↥F₁ {w' | w'.under (𝓞 ℚ) ∈ T})
  (hJinf : ∀ z : (AdeleRing (𝓞 ↥F) ↥F)ˣ, infPart z = 1 → infPart (Units.map (J : AdeleRing (𝓞 ↥F) ↥F →* AdeleRing (𝓞 ↥F₁) ↥F₁) z) = 1)
  (j : Rep.res (levelMapR F F₁ hle.out) (Rep.ofMulDistribMulAction (↥F ≃ₐ[ℚ] ↥F) (IdeleClassGroup (𝓞 ↥F) ↥F)) ⟶
    Rep.ofMulDistribMulAction (↥F₁ ≃ₐ[ℚ] ↥F₁) (IdeleClassGroup (𝓞 ↥F₁) ↥F₁))
  (hj : ∀ x : (AdeleRing (𝓞 ↥F) ↥F)ˣ, j.hom (Additive.ofMul (QuotientGroup.mk x : IdeleClassGroup (𝓞 ↥F) ↥F)) =
    Additive.ofMul (QuotientGroup.mk (JJ F F₁ J x) : IdeleClassGroup (𝓞 ↥F₁) ↥F₁))
  (hvii : ∀ x, sys₁.invG ((groupCohomology.map (levelMapR F F₁ hle.out) j 2).hom x) = sys.invG x)

include hunr hunr₁ hj hvii in

theorem hjC (c : ↥(groupCohomology (CS S F) 2)) :
    invGSFs S F₁ hunr₁ sys₁ ((groupCohomology.map (levelMapR F F₁ hle.out) (jC S F F₁ J hJF hJeq hJout hJunit hJinf) 2).hom c) =
      invGSFs S F hunr sys c := by
  obtain ⟨c₀, rfl⟩ := (qG_bijective (qSF S F) (qSF_bijective S F hunr) sys.invG sys.inv sys.hinj sys.hrangeG sys.hrange sys.hii).2 c
  have h1 := groupCohomology.map_comp (MonoidHom.id (↥F ≃ₐ[ℚ] ↥F)) (levelMapR F F₁ hle.out)
    (show Rep.res (MonoidHom.id (↥F ≃ₐ[ℚ] ↥F)) (Rep.ofMulDistribMulAction (↥F ≃ₐ[ℚ] ↥F) (IdeleClassGroup (𝓞 ↥F) ↥F)) ⟶ CS S F from qSF S F)
    (jC S F F₁ J hJF hJeq hJout hJunit hJinf) 2
  have h2 := groupCohomology.map_comp (levelMapR F F₁ hle.out) (MonoidHom.id (↥F₁ ≃ₐ[ℚ] ↥F₁)) j
    (show Rep.res (MonoidHom.id (↥F₁ ≃ₐ[ℚ] ↥F₁)) (Rep.ofMulDistribMulAction (↥F₁ ≃ₐ[ℚ] ↥F₁) (IdeleClassGroup (𝓞 ↥F₁) ↥F₁)) ⟶ CS S F₁ from qSF S F₁) 2
  rw [hsq_qSF S F F₁ J hJF hJeq hJout hJunit hJinf j hj] at h1
  have h12 : groupCohomology.map (MonoidHom.id _) (qSF S F) 2 ≫ groupCohomology.map (levelMapR F F₁ hle.out) (jC S F F₁ J hJF hJeq hJout hJunit hJinf) 2 =
      groupCohomology.map (levelMapR F F₁ hle.out) j 2 ≫ groupCohomology.map (MonoidHom.id _) (qSF S F₁) 2 := by
    rw [← h1, ← h2]; rfl
  have h3 := congrArg (fun φ => (ModuleCat.Hom.hom φ) c₀) h12
  change (groupCohomology.map (levelMapR F F₁ hle.out) (jC S F F₁ J hJF hJeq hJout hJunit hJinf) 2).hom
      ((groupCohomology.map (MonoidHom.id _) (qSF S F) 2).hom c₀) =
    (groupCohomology.map (MonoidHom.id _) (qSF S F₁) 2).hom ((groupCohomology.map (levelMapR F F₁ hle.out) j 2).hom c₀) at h3
  rw [h3, invGSFs_apply S F₁ hunr₁ sys₁, hvii, invGSFs_apply S F hunr sys]

end towerInv
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

end Reduce95
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
open CategoryTheory IsDedekindDomain NumberField

namespace Reduce95
open ExtCitation groupCohomology M4aHerbrand
open scoped NumberField.PlaceDecomp

section invinfl

variable {p : ℕ} [Fact p.Prime] (F F₁ : IntermediateField ℚ (AlgebraicClosure ℚ))
  [NumberField ↥F] [IsGalois ℚ ↥F] [NumberField ↥F₁] [IsGalois ℚ ↥F₁] [hle : Fact (F ≤ F₁)]

set_option maxHeartbeats 3200000 in

theorem invinfl_sys (hp2 : p ≠ 2) (sys₁ : InvSys F₁)
    (hiii₁ : ∀ (w : HeightOneSpectrum (𝓞 ↥F₁))
        (q : ℕ) [Fact q.Prime] (L' : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L']
        [MulSemiringAction (↥(NumberField.PlaceDecomp.decomp ℚ ↥F₁ w)) L'] [MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp ℚ ↥F₁ w)) (↥L')ˣ]
        (Φ : w.adicCompletion ↥F₁ ≃+* L')
        (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F₁ w)) (x : ℚ_[q]), g • algebraMap ℚ_[q] L' x = algebraMap ℚ_[q] L' x)
        (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F₁ w)) (v : (↥L')ˣ), ((g • v : (↥L')ˣ) : L') = g • (v : L'))
        (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F₁ w)) (x : w.adicCompletion ↥F₁), Φ (g • x) = g • Φ x)
        (K₀ : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K₀]
        (_ : ExtCitation.LocalLevel.IsBase q L' (↥(NumberField.PlaceDecomp.decomp ℚ ↥F₁ w)) K₀)
        (θ : Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp ℚ ↥F₁ w)) (↥L')ˣ ⟶
          Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp ℚ ↥F₁ w)) (w.adicCompletion ↥F₁)ˣ)
        (_ : ∀ v : (↥L')ˣ, ((Additive.toMul (θ.hom (Additive.ofMul v)) : (w.adicCompletion ↥F₁)ˣ) : w.adicCompletion ↥F₁) = Φ.symm (v : L'))
        (u' : groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp ℚ ↥F₁ w)) (↥L')ˣ))
        (_ : ExtCitation.LocalLevel.IsLocalFundamentalClass q L' (↥(NumberField.PlaceDecomp.decomp ℚ ↥F₁ w)) K₀ u'),
        ∀ (m a : ℕ) (_ : p.Coprime m) (_ : m * p ^ a = Nat.card ↥(NumberField.PlaceDecomp.decomp ℚ ↥F₁ w)),
        m • sys₁.inv (NumberField.PlaceDecomp.decomp ℚ ↥F₁ w)
            ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp ℚ ↥F₁ w)) (lamWF F₁ w) 2).hom
              ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp ℚ ↥F₁ w)) θ 2).hom u')) =
          (((m : ℚ) / (Nat.card ↥(NumberField.PlaceDecomp.decomp ℚ ↥F₁ w) : ℚ) : ℚ) : AddCircle (1 : ℚ))) :
    ∃ (J : AdeleRing (𝓞 ↥F) ↥F →+* AdeleRing (𝓞 ↥F₁) ↥F₁)
      (_ : Continuous J)
      (_ : ∀ a : ↥F, J (algebraMap ↥F (AdeleRing (𝓞 ↥F) ↥F) a) = algebraMap ↥F₁ (AdeleRing (𝓞 ↥F₁) ↥F₁) (algebraMap ↥F ↥F₁ a))
      (_ : ∀ (g' : ↥F₁ ≃ₐ[ℚ] ↥F₁) (x : AdeleRing (𝓞 ↥F) ↥F), J ((DD F).act (AlgEquiv.restrictNormalHom ↥F g') x) = (DD F₁).act g' (J x))
      (_ : ∀ (T : Set (HeightOneSpectrum (𝓞 ℚ))) (z : (AdeleRing (𝓞 ↥F) ↥F)ˣ),
        (∀ w : HeightOneSpectrum (𝓞 ↥F), w.under (𝓞 ℚ) ∉ T → finPart w z = 1) →
        ∀ w' : HeightOneSpectrum (𝓞 ↥F₁), w'.under (𝓞 ℚ) ∉ T →
          finPart w' (Units.map (J : AdeleRing (𝓞 ↥F) ↥F →* AdeleRing (𝓞 ↥F₁) ↥F₁) z) = 1)
      (_ : ∀ (T : Set (HeightOneSpectrum (𝓞 ℚ))) (z : (AdeleRing (𝓞 ↥F) ↥F)ˣ),
        z ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 ↥F) ↥F {w | w.under (𝓞 ℚ) ∈ T} →
        Units.map (J : AdeleRing (𝓞 ↥F) ↥F →* AdeleRing (𝓞 ↥F₁) ↥F₁) z ∈
          NumberField.AdeleRing.unitIdelesOutside (𝓞 ↥F₁) ↥F₁ {w' | w'.under (𝓞 ℚ) ∈ T})
      (_ : ∀ z : (AdeleRing (𝓞 ↥F) ↥F)ˣ, infPart z = 1 → infPart (Units.map (J : AdeleRing (𝓞 ↥F) ↥F →* AdeleRing (𝓞 ↥F₁) ↥F₁) z) = 1)
      (_ : ∀ (z z' : (AdeleRing (𝓞 ↥F) ↥F)ˣ) (w' : HeightOneSpectrum (𝓞 ↥F₁)),
        finPart (w'.under (𝓞 ↥F)) z = finPart (w'.under (𝓞 ↥F)) z' → finPart w' (JJ F F₁ J z) = finPart w' (JJ F F₁ J z'))
      (j : Rep.res (levelMapR F F₁ hle.out) (Rep.ofMulDistribMulAction (↥F ≃ₐ[ℚ] ↥F) (IdeleClassGroup (𝓞 ↥F) ↥F)) ⟶
        Rep.ofMulDistribMulAction (↥F₁ ≃ₐ[ℚ] ↥F₁) (IdeleClassGroup (𝓞 ↥F₁) ↥F₁))
      (_ : ∀ x : (AdeleRing (𝓞 ↥F) ↥F)ˣ, j.hom (Additive.ofMul (QuotientGroup.mk x : IdeleClassGroup (𝓞 ↥F) ↥F)) =
        Additive.ofMul (QuotientGroup.mk (JJ F F₁ J x) : IdeleClassGroup (𝓞 ↥F₁) ↥F₁))
      (sys₀ : InvSys F)
      (_ : ∀ (w : HeightOneSpectrum (𝓞 ↥F))
        (q : ℕ) [Fact q.Prime] (L' : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L']
        [MulSemiringAction (↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) L'] [MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (↥L')ˣ]
        (Φ : w.adicCompletion ↥F ≃+* L')
        (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (x : ℚ_[q]), g • algebraMap ℚ_[q] L' x = algebraMap ℚ_[q] L' x)
        (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (v : (↥L')ˣ), ((g • v : (↥L')ˣ) : L') = g • (v : L'))
        (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (x : w.adicCompletion ↥F), Φ (g • x) = g • Φ x)
        (K₀ : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K₀]
        (_ : ExtCitation.LocalLevel.IsBase q L' (↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) K₀)
        (θ : Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (↥L')ˣ ⟶
          Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (w.adicCompletion ↥F)ˣ)
        (_ : ∀ v : (↥L')ˣ, ((Additive.toMul (θ.hom (Additive.ofMul v)) : (w.adicCompletion ↥F)ˣ) : w.adicCompletion ↥F) = Φ.symm (v : L'))
        (u' : groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (↥L')ˣ))
        (_ : ExtCitation.LocalLevel.IsLocalFundamentalClass q L' (↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) K₀ u'),
        ∀ (m a : ℕ) (_ : p.Coprime m) (_ : m * p ^ a = Nat.card ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)),
        m • sys₀.inv (NumberField.PlaceDecomp.decomp ℚ ↥F w)
            ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (lamWF F w) 2).hom
              ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) θ 2).hom u')) =
          (((m : ℚ) / (Nat.card ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) : ℚ) : ℚ) : AddCircle (1 : ℚ))),
      ∀ x, sys₁.invG ((groupCohomology.map (levelMapR F F₁ hle.out) j 2).hom x) = sys₀.invG x := by
  obtain ⟨J, j, invG, inv, ⟨hJcont, hJF, hJeq, hJout, hJunit, hJinf, hJloc⟩, ⟨hj, -, -⟩, hinjG, hinj, hrangeG, hrange, hii, hiii, hv, hvii⟩ :=
    M4aHerbrand.exists_adeleBaseChange_invariant_groupCohomology_ideleClassGroup_map_eq_of_invariant p hp2 ℚ ↥F ↥F₁
      (DD F) (hact_F F) (iotaW ↥F) (iotaW_spec ↥F) (lamWF F) (lamWF_apply F)
      (DD F₁) (hact_F F₁) (iotaW ↥F₁) (iotaW_spec ↥F₁) (lamWF F₁) (lamWF_apply F₁)
      sys₁.invG sys₁.inv ⟨sys₁.hinjG, sys₁.hinj, sys₁.hrangeG, sys₁.hrange, sys₁.hii, hiii₁, sys₁.hv⟩
  exact ⟨J, hJcont, hJF, hJeq, hJout, hJunit, hJinf, hJloc, j, hj, ⟨invG, inv, hinjG, hinj, hrangeG, hrange, hii, hv⟩, hiii, hvii⟩

end invinfl
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

end Reduce95
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
open CategoryTheory IsDedekindDomain NumberField

namespace Reduce95
open ExtCitation groupCohomology GroupCohomology M4aHerbrand
open scoped NumberField.PlaceDecomp

section stdp

variable (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F]

def INV_Fp := M4aHerbrand.exists_invariant_groupCohomology_ideleClassGroup_forall_comp_eq_index_smul_of_ne_two p hp2 ℚ ↥F
  (DD F) (hact_F F) (iotaW ↥F) (iotaW_spec ↥F) (lamWF F) (lamWF_apply F)

def INV_Fp_spec := (INV_Fp p hp2 F).choose_spec.choose_spec

noncomputable def InvSys.stdp : InvSys F where
  invG := (INV_Fp p hp2 F).choose
  inv := (INV_Fp p hp2 F).choose_spec.choose
  hinjG := (INV_Fp_spec p hp2 F).1
  hinj := (INV_Fp_spec p hp2 F).2.1
  hrangeG := (INV_Fp_spec p hp2 F).2.2.1
  hrange := (INV_Fp_spec p hp2 F).2.2.2.1
  hii := (INV_Fp_spec p hp2 F).2.2.2.2.1
  hv := (INV_Fp_spec p hp2 F).2.2.2.2.2.2

theorem InvSys.stdp_iii' :
    ∀ (w : HeightOneSpectrum (𝓞 ↥F))
        (q : ℕ) [Fact q.Prime] (L' : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L']
        [MulSemiringAction (↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) L'] [MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (↥L')ˣ]
        (Φ : w.adicCompletion ↥F ≃+* L')
        (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (x : ℚ_[q]), g • algebraMap ℚ_[q] L' x = algebraMap ℚ_[q] L' x)
        (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (v : (↥L')ˣ), ((g • v : (↥L')ˣ) : L') = g • (v : L'))
        (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (x : w.adicCompletion ↥F), Φ (g • x) = g • Φ x)
        (K₀ : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K₀]
        (_ : ExtCitation.LocalLevel.IsBase q L' (↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) K₀)
        (θ : Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (↥L')ˣ ⟶
          Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (w.adicCompletion ↥F)ˣ)
        (_ : ∀ v : (↥L')ˣ, ((Additive.toMul (θ.hom (Additive.ofMul v)) : (w.adicCompletion ↥F)ˣ) : w.adicCompletion ↥F) = Φ.symm (v : L'))
        (u' : groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (↥L')ˣ))
        (_ : ExtCitation.LocalLevel.IsLocalFundamentalClass q L' (↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) K₀ u'),
        ∀ (m a : ℕ) (_ : p.Coprime m) (_ : m * p ^ a = Nat.card ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)),
        m • (InvSys.stdp p hp2 F).inv (NumberField.PlaceDecomp.decomp ℚ ↥F w)
            ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (lamWF F w) 2).hom
              ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) θ 2).hom u')) =
          (((m : ℚ) / (Nat.card ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) : ℚ) : ℚ) : AddCircle (1 : ℚ)) :=
  (INV_Fp_spec p hp2 F).2.2.2.2.2.1

end stdp
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

section uQp
variable {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (q : ↥S) (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p)

local instance factPrimesUQp (q : Nat.Primes) : Fact ((q : ℕ)).Prime := ⟨q.2⟩

noncomputable def uQp : (ZMod p)ˣ :=
  (NumberField.PlaceDecomp.exists_unit_inv_map_delta_res_eq_theta_localBridge_primary S q ζ hζ).choose

def uQp_spec := (NumberField.PlaceDecomp.exists_unit_inv_map_delta_res_eq_theta_localBridge_primary S q ζ hζ).choose_spec

end uQp
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

section hLOCfins
variable {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
  [FiniteDimensional (ZMod p) M] (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p)
  (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F]
  (B : Rep ℤ (↥F ≃ₐ[ℚ] ↥F)) [Fintype B] (β : B →+ M.dualTwist (cycloChar p))
  (hβeq : ∀ (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (b : B),
    β (B.ρ (AlgEquiv.restrictNormalHom ↥F γ) b) = (M.dualTwist (cycloChar p)).ρ γ (β b))
  (hβ : Function.Bijective β) (hB : ∀ b : B, p • b = 0)
  (hunr : ∀ w : HeightOneSpectrum (𝓞 ↥F), w ∉ TT S F → Ideal.ramificationIdx' (w.asIdeal.under (𝓞 ℚ)) w.asIdeal = 1)
  (sys : InvSys F)
  (hiii : ∀ (w : HeightOneSpectrum (𝓞 ↥F))
        (q : ℕ) [Fact q.Prime] (L' : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L']
        [MulSemiringAction (↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) L'] [MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (↥L')ˣ]
        (Φ : w.adicCompletion ↥F ≃+* L')
        (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (x : ℚ_[q]), g • algebraMap ℚ_[q] L' x = algebraMap ℚ_[q] L' x)
        (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (v : (↥L')ˣ), ((g • v : (↥L')ˣ) : L') = g • (v : L'))
        (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (x : w.adicCompletion ↥F), Φ (g • x) = g • Φ x)
        (K₀ : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K₀]
        (_ : ExtCitation.LocalLevel.IsBase q L' (↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) K₀)
        (θ : Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (↥L')ˣ ⟶
          Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (w.adicCompletion ↥F)ˣ)
        (_ : ∀ v : (↥L')ˣ, ((Additive.toMul (θ.hom (Additive.ofMul v)) : (w.adicCompletion ↥F)ˣ) : w.adicCompletion ↥F) = Φ.symm (v : L'))
        (u' : groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (↥L')ˣ))
        (_ : ExtCitation.LocalLevel.IsLocalFundamentalClass q L' (↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) K₀ u'),
        ∀ (m a : ℕ) (_ : p.Coprime m) (_ : m * p ^ a = Nat.card ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)),
        m • sys.inv (NumberField.PlaceDecomp.decomp ℚ ↥F w)
            ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (lamWF F w) 2).hom
              ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) θ 2).hom u')) =
          (((m : ℚ) / (Nat.card ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) : ℚ) : ℚ) : AddCircle (1 : ℚ)))

local instance factPrimesLs (q : Nat.Primes) : Fact ((q : ℕ)).Prime := ⟨q.2⟩

include hunr in
set_option maxHeartbeats 6400000 in

theorem invSFs_map_comp_qSF (H : Subgroup (↥F ≃ₐ[ℚ] ↥F)) {X Y : Rep ℤ ↥H} (s : X ⟶ Y)
    (l : Y ⟶ Rep.res H.subtype (Rep.ofMulDistribMulAction (↥F ≃ₐ[ℚ] ↥F) (IdeleClassGroup (𝓞 ↥F) ↥F)))
    (y : groupCohomology X 2) :
    invSFs S F hunr sys H ((groupCohomology.map (MonoidHom.id ↥H) (s ≫ l ≫ (Rep.resFunctor H.subtype).map (qSF S F)) 2).hom y) =
      sys.inv H ((groupCohomology.map (MonoidHom.id ↥H) (s ≫ l) 2).hom y) := by
  rw [← Category.assoc, groupCohomology.map_id_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
  exact inv'_apply (qSF S F) (qSF_bijective S F hunr) sys.inv H _

include hiii in
set_option maxHeartbeats 16000000 in

theorem hLOC_fin_s (q : ↥S)
    (θq : continuousH1 (extArithLoc S (Sum.inr q)) (Rep.res (extArithLoc S (Sum.inr q)) M) →ₗ[ZMod p]
        Module.Dual (ZMod p) (continuousH1 (extArithLoc S (Sum.inr q)) (Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p)))))
    (hθq : IsTheta1 (extArithLoc S (Sum.inr q))
        (Module.Dual.eval (ZMod p) M :
          Rep.res (extArithLoc S (Sum.inr q)) M →ₗ[ZMod p]
            Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p)) →ₗ[ZMod p]
              ofChar (k := ZMod p) ((cycloChar p).comp (extArithLoc S (Sum.inr q))))
        (localInv p ζ (q : Nat.Primes)) θq)
    (hloc : ∀ y ∈ continuousH1S S (M.dualTwist (cycloChar p)), ∀ v : extArithIndex S,
      locTotal (extArithLoc S) (M.dualTwist (cycloChar p)) y v ∈ continuousH1 (extArithLoc S v) (Rep.res (extArithLoc S v) (M.dualTwist (cycloChar p))))
    (infl : groupCohomology B 1 →+ H1 (M.dualTwist (cycloChar p)))
    (hinflpin : ∀ (n : cocycles₁ B) (ny : cocycles₁ (M.dualTwist (cycloChar p))),
        (∀ γ, ny γ = β (n (AlgEquiv.restrictNormalHom ↥F γ))) →
          infl ((H1π B).hom n) = (H1π (M.dualTwist (cycloChar p))).hom ny)
    (sv : Rep.res (Dv S F (Sum.inr q)).subtype (Rep.relationModuleInt B) ⟶ Yv S F (Sum.inr q)) (x : groupCohomology B 1)
    (hx : infl x ∈ continuousH1S S (M.dualTwist (cycloChar p))) :
    invSFs S F hunr sys (Dv S F (Sum.inr q))
      ((groupCohomology.map (MonoidHom.id ↥(Dv S F (Sum.inr q))) (sv ≫ lamV S F (LF S F) (Sum.inr q)) 2).hom
        ((groupCohomology.δ (hXvB S F B (Sum.inr q)) 1 2 rfl).hom
          ((groupCohomology.map (Dv S F (Sum.inr q)).subtype (𝟙 (Rep.res (Dv S F (Sum.inr q)).subtype B)) 1).hom x)))
      = (((((uQp S q ζ hζ : ZMod p) * θq (LamQc' M ζ hζ F B β hβeq hβ hB q.1 sv)
            ⟨locTotal (extArithLoc S) (M.dualTwist (cycloChar p)) (infl x) (Sum.inr q), hloc _ hx _⟩).val : ℚ) / (p : ℚ) : ℚ) :
          AddCircle (1 : ℚ)) := by
  classical
  obtain ⟨n, rfl⟩ := (ModuleCat.epi_iff_surjective (H1π B)).1 inferInstance x
  have hny : ∀ γ, inflC' M F B β hβeq n γ = β (n (AlgEquiv.restrictNormalHom ↥F γ)) := fun _ => rfl
  have hxy : infl ((H1π B).hom n) = (H1π (M.dualTwist (cycloChar p))).hom (inflC' M F B β hβeq n) := hinflpin n _ hny
  rw [lamV_inr_eq_F S F q]
  refine (invSFs_map_comp_qSF S F hunr sys _ sv (lamWF F (wq F q.1)) _).trans ?_
  exact uQp_spec S q ζ hζ M F (wq F q.1) (sigmaQ F q.1) (PhiQ F q.1) (hPhiF_q F q.1) (hcont_q F q.1) (piQ F q.1) (hpi_q F q.1)
    (hpisurj_q F q.1) (heqv_q F q.1) (Rep.relationSeqInt B) (Rep.relationSeqInt_shortExact B)
    (hXvB S F B (Sum.inr q)) hB (kappa M ζ hζ B β) (kappa_equivariant M ζ hζ (AlgEquiv.restrictNormalHom ↥F) B β hβeq)
    (kappa_perfect M ζ hζ B β hβ hB) β
    (coe_toMul_kappa M ζ hζ B β) (kappaQF M F q.1 B (kappa M ζ hζ B β))
    (toMul_kappaQ M ((q : Nat.Primes) : ℕ) (sigmaQ F q.1) B (kappa M ζ hζ B β)) (DD F) (hact_F F)
    (iotaW ↥F (wq F q.1)) (iotaW_spec ↥F (wq F q.1)) (lamWF F (wq F q.1)) (lamWF_apply F (wq F q.1))
    (sys.inv _) (sys.hinj _) (hiii (wq F q.1) ((q : Nat.Primes) : ℕ))
    (LamQ' M ζ hζ F B β hβeq hβ hB q.1) (LamQ'_bridge M ζ hζ F B β hβeq hβ hB q.1) θq hθq sv n (inflC' M F B β hβeq n) hny
    (LamQc' M ζ hζ F B β hβeq hβ hB q.1 sv) rfl
    ⟨locTotal (extArithLoc S) (M.dualTwist (cycloChar p)) (infl ((H1π B).hom n)) (Sum.inr q), hloc _ hx _⟩
    (by rw [← hxy]; rfl)

end hLOCfins
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

section hLOCinfs
variable {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
  [FiniteDimensional (ZMod p) M]
  (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F]
  (B : Rep ℤ (↥F ≃ₐ[ℚ] ↥F)) (hB : ∀ b : B, p • b = 0)
  (hunr : ∀ w : HeightOneSpectrum (𝓞 ↥F), w ∉ TT S F → Ideal.ramificationIdx' (w.asIdeal.under (𝓞 ℚ)) w.asIdeal = 1)
  (sys : InvSys F)

include hB in
set_option maxHeartbeats 16000000 in

theorem hLOC_inf_s (hp2 : p ≠ 2) (u : Unit)
    (θu : continuousH1 (extArithLoc S (Sum.inl u)) (Rep.res (extArithLoc S (Sum.inl u)) M) →ₗ[ZMod p]
        Module.Dual (ZMod p) (continuousH1 (extArithLoc S (Sum.inl u)) (Rep.res (extArithLoc S (Sum.inl u)) (M.dualTwist (cycloChar p)))))
    (Λu : (Rep.res (Dv S F (Sum.inl u)).subtype (Rep.relationModuleInt B) ⟶ Yv S F (Sum.inl u)) →+
        ↥(continuousH1 (extArithLoc S (Sum.inl u)) (Rep.res (extArithLoc S (Sum.inl u)) M)))
    (hloc : ∀ y ∈ continuousH1S S (M.dualTwist (cycloChar p)), ∀ v : extArithIndex S,
      locTotal (extArithLoc S) (M.dualTwist (cycloChar p)) y v ∈ continuousH1 (extArithLoc S v) (Rep.res (extArithLoc S v) (M.dualTwist (cycloChar p))))
    (infl : groupCohomology B 1 →+ H1 (M.dualTwist (cycloChar p)))
    (sv : Rep.res (Dv S F (Sum.inl u)).subtype (Rep.relationModuleInt B) ⟶ Yv S F (Sum.inl u)) (x : groupCohomology B 1)
    (hx : infl x ∈ continuousH1S S (M.dualTwist (cycloChar p))) :
    invSFs S F hunr sys (Dv S F (Sum.inl u))
      ((groupCohomology.map (MonoidHom.id ↥(Dv S F (Sum.inl u))) (sv ≫ lamV S F (LF S F) (Sum.inl u)) 2).hom
        ((groupCohomology.δ (hXvB S F B (Sum.inl u)) 1 2 rfl).hom
          ((groupCohomology.map (Dv S F (Sum.inl u)).subtype (𝟙 (Rep.res (Dv S F (Sum.inl u)).subtype B)) 1).hom x)))
      = ((((((1 : (ZMod p)ˣ) : ZMod p) * θu (Λu sv)
            ⟨locTotal (extArithLoc S) (M.dualTwist (cycloChar p)) (infl x) (Sum.inl u), hloc _ hx _⟩).val : ℚ) / (p : ℚ) : ℚ) :
          AddCircle (1 : ℚ)) := by
  classical

  have hz0 : ∀ z : H1 (Rep.res (extArithLoc S (Sum.inl u)) (M.dualTwist (cycloChar p))), z = 0 := by
    intro z
    by_contra hz
    have h1 : Module.finrank (ZMod p) ↥((ZMod p) ∙ z) = 1 := finrank_span_singleton hz
    have h0 := groupCohomology.finrank_submodule_res_extArithLoc_archSlot_eq_zero hp2 S (M.dualTwist (cycloChar p)) u ((ZMod p) ∙ z)
    omega
  have hw : (⟨locTotal (extArithLoc S) (M.dualTwist (cycloChar p)) (infl x) (Sum.inl u), hloc _ hx _⟩ :
      ↥(continuousH1 (extArithLoc S (Sum.inl u)) (Rep.res (extArithLoc S (Sum.inl u)) (M.dualTwist (cycloChar p))))) = 0 :=
    Submodule.coe_eq_zero.1 (hz0 _)
  rw [hw, map_zero, mul_zero, ZMod.val_zero, Nat.cast_zero, zero_div, AddCircle.coe_zero]

  obtain ⟨n, rfl⟩ := (ModuleCat.epi_iff_surjective (H1π B)).1 inferInstance x
  have hn0 : (p : ℤ) • n = 0 := by
    apply Subtype.ext
    funext g
    show (p : ℤ) • n g = 0
    rw [natCast_zsmul]
    exact hB (n g)
  have hpz := zsmul_hom4_eq_zero_e2 (H1π B)
    (groupCohomology.map (Dv S F (Sum.inl u)).subtype (𝟙 (Rep.res (Dv S F (Sum.inl u)).subtype B)) 1)
    (groupCohomology.δ (hXvB S F B (Sum.inl u)) 1 2 rfl)
    (groupCohomology.map (MonoidHom.id ↥(Dv S F (Sum.inl u))) (sv ≫ lamV S F (LF S F) (Sum.inl u)) 2) n (p : ℤ) hn0
  haveI : Fintype ↥(Dv S F (Sum.inl u)) := Fintype.ofFinite _
  have hDz := Rep.card_smul_eq_zero_of_tateCohomology
    (Rep.res (Dv S F (Sum.inl u)).subtype (Rep.ofMulDistribMulAction (↥F ≃ₐ[ℚ] ↥F) (SIdeleClassGroup (𝓞 ↥F) ↥F (TT S F))))
    ((1 + 1 : ℕ) : ℤ)
    (show ↥((Rep.res (Dv S F (Sum.inl u)).subtype
        (Rep.ofMulDistribMulAction (↥F ≃ₐ[ℚ] ↥F) (SIdeleClassGroup (𝓞 ↥F) ↥F (TT S F)))).tateCohomology ((1 + 1 : ℕ) : ℤ)) from
      (groupCohomology.map (MonoidHom.id ↥(Dv S F (Sum.inl u))) (sv ≫ lamV S F (LF S F) (Sum.inl u)) 2).hom
        ((groupCohomology.δ (hXvB S F B (Sum.inl u)) 1 2 rfl).hom
          ((groupCohomology.map (Dv S F (Sum.inl u)).subtype (𝟙 (Rep.res (Dv S F (Sum.inl u)).subtype B)) 1).hom
            ((H1π B).hom n))))
  have hcard : Nat.card ↥(Dv S F (Sum.inl u)) = 1 ∨ Nat.card ↥(Dv S F (Sum.inl u)) = 2 :=
    NumberField.InfinitePlace.nat_card_stabilizer_eq_one_or_two ℚ (NumberField.ArchIdele.above ℚ ↥F default)
  have hcop : IsCoprime (p : ℤ) (Fintype.card ↥(Dv S F (Sum.inl u)) : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast, Fintype.card_eq_nat_card]
    rcases hcard with h | h
    · rw [h]; exact Nat.coprime_one_right p
    · rw [h]; exact (Nat.coprime_primes Fact.out Nat.prime_two).2 hp2
  exact (congrArg (invSFs S F hunr sys (Dv S F (Sum.inl u))) (eq_zero_of_zsmul_of_isCoprime hcop _ hpz ((module_zsmul_eq _ _).symm.trans hDz))).trans
    (map_zero _)

end hLOCinfs
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

section hLOCalls
open scoped Classical

variable {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes)
  (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) [FiniteDimensional (ZMod p) M]
  (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p)
  (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F] [IsTotallyComplex ↥F]
  (hζF : ζ ∈ F)
  (hunr : ∀ w : HeightOneSpectrum (𝓞 ↥F), w ∉ TT S F → Ideal.ramificationIdx' (w.asIdeal.under (𝓞 ℚ)) w.asIdeal = 1)
  (sys : InvSys F)
  (hiii : ∀ (w : HeightOneSpectrum (𝓞 ↥F))
        (q : ℕ) [Fact q.Prime] (L' : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L']
        [MulSemiringAction (↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) L'] [MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (↥L')ˣ]
        (Φ : w.adicCompletion ↥F ≃+* L')
        (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (x : ℚ_[q]), g • algebraMap ℚ_[q] L' x = algebraMap ℚ_[q] L' x)
        (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (v : (↥L')ˣ), ((g • v : (↥L')ˣ) : L') = g • (v : L'))
        (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (x : w.adicCompletion ↥F), Φ (g • x) = g • Φ x)
        (K₀ : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K₀]
        (_ : ExtCitation.LocalLevel.IsBase q L' (↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) K₀)
        (θ : Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (↥L')ˣ ⟶
          Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (w.adicCompletion ↥F)ˣ)
        (_ : ∀ v : (↥L')ˣ, ((Additive.toMul (θ.hom (Additive.ofMul v)) : (w.adicCompletion ↥F)ˣ) : w.adicCompletion ↥F) = Φ.symm (v : L'))
        (u' : groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (↥L')ˣ))
        (_ : ExtCitation.LocalLevel.IsLocalFundamentalClass q L' (↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) K₀ u'),
        ∀ (m a : ℕ) (_ : p.Coprime m) (_ : m * p ^ a = Nat.card ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)),
        m • sys.inv (NumberField.PlaceDecomp.decomp ℚ ↥F w)
            ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (lamWF F w) 2).hom
              ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) θ 2).hom u')) =
          (((m : ℚ) / (Nat.card ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) : ℚ) : ℚ) : AddCircle (1 : ℚ)))
  (B : Rep ℤ (↥F ≃ₐ[ℚ] ↥F)) [Fintype B] (β : B →+ M.dualTwist (cycloChar p))
  (hβeq : ∀ (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (b : B),
    β (B.ρ (AlgEquiv.restrictNormalHom ↥F γ) b) = (M.dualTwist (cycloChar p)).ρ γ (β b))
  (hβ : Function.Bijective β) (hB : ∀ b : B, p • b = 0)
  (hp2 : p ≠ 2)

local instance factPrimesLa (q : Nat.Primes) : Fact ((q : ℕ)).Prime := ⟨q.2⟩

noncomputable def uVp : extArithIndex S → (ZMod p)ˣ
  | Sum.inl _ => 1
  | Sum.inr q => uQp S q ζ hζ

variable
  (θ : ∀ v : extArithIndex S,
    continuousH1 (extArithLoc S v) (Rep.res (extArithLoc S v) M) →ₗ[ZMod p]
      Module.Dual (ZMod p) (continuousH1 (extArithLoc S v) (Rep.res (extArithLoc S v) (M.dualTwist (cycloChar p)))))
  (hθ : ∀ q : ↥S, IsTheta1 (extArithLoc S (Sum.inr q))
        (Module.Dual.eval (ZMod p) M :
          Rep.res (extArithLoc S (Sum.inr q)) M →ₗ[ZMod p]
            Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p)) →ₗ[ZMod p]
              ofChar (k := ZMod p) ((cycloChar p).comp (extArithLoc S (Sum.inr q))))
        (localInv p ζ (q : Nat.Primes)) (θ (Sum.inr q)))
  (hloc : ∀ y ∈ continuousH1S S (M.dualTwist (cycloChar p)), ∀ v : extArithIndex S,
    locTotal (extArithLoc S) (M.dualTwist (cycloChar p)) y v ∈ continuousH1 (extArithLoc S v) (Rep.res (extArithLoc S v) (M.dualTwist (cycloChar p))))
  (infl : ↥(groupCohomology B 1) →+ H1 (M.dualTwist (cycloChar p)))
  (hinflpin : ∀ (n : cocycles₁ B) (ny : cocycles₁ (M.dualTwist (cycloChar p))),
      (∀ γ, ny γ = β (n (AlgEquiv.restrictNormalHom ↥F γ))) →
        infl ((H1π B).hom n) = (H1π (M.dualTwist (cycloChar p))).hom ny)

include hθ hinflpin hp2 hiii in

theorem hLOC_s : ∀ (v : extArithIndex S) (sv : Rep.res (Dv S F v).subtype (Rep.relationModuleInt B) ⟶ Yv S F v)
      (x : ↥(groupCohomology B 1)) (hx : infl x ∈ continuousH1S S (M.dualTwist (cycloChar p))),
    invSFs S F hunr sys (Dv S F v) ((groupCohomology.map (MonoidHom.id ↥(Dv S F v)) (sv ≫ lamV S F (LF S F) v) 2).hom
      ((groupCohomology.δ (hXv' S F B v) 1 2 rfl).hom
        ((groupCohomology.map (Dv S F v).subtype (𝟙 (Rep.res (Dv S F v).subtype B)) 1).hom x)))
      = (((((uVp S ζ hζ v : ZMod p) * θ v (LamV S M ζ hζ F hζF B β hβeq hβ hB v sv)
          ⟨locTotal (extArithLoc S) (M.dualTwist (cycloChar p)) (infl x) v, hloc _ hx v⟩).val : ℚ) / (p : ℚ) : ℚ) : AddCircle (1 : ℚ))
  | Sum.inl u, sv, x, hx => hLOC_inf_s S M F B hB hunr sys hp2 u (θ (Sum.inl u)) (LamV S M ζ hζ F hζF B β hβeq hβ hB (Sum.inl u)) hloc infl sv x hx
  | Sum.inr q, sv, x, hx => hLOC_fin_s S M ζ hζ F B β hβeq hβ hB hunr sys hiii q (θ (Sum.inr q)) (hθ q) hloc infl hinflpin sv x hx

include hθ hinflpin hp2 hiii in

theorem hID_s (s : Rep.relationModuleInt B ⟶ NumberField.SArchIdele.obj ℚ ↥F (Sq S)) (x : ↥(groupCohomology B 1))
    (hx : infl x ∈ continuousH1S S (M.dualTwist (cycloChar p))) :
    alFs S F hunr sys B hB (s ≫ (seqF S F).g ≫ RepImage.ι (LF S F)) x =
      ∑ v, (uVp S ζ hζ v : ZMod p) * θ v (LJ1 S M ζ hζ F hζF B β hβeq hβ hB s v)
        ⟨locTotal (extArithLoc S) (M.dualTwist (cycloChar p)) (infl x) v, hloc _ hx v⟩ :=
  hIDs S M ζ hζ F hζF hunr sys B β hβeq hβ hB θ hloc infl (uVp S ζ hζ) (hLOC_s S M ζ hζ F hζF hunr sys hiii B β hβeq hβ hB hp2 θ hθ hloc infl hinflpin) s x hx

end hLOCalls
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

section check
variable {p : ℕ} [Fact p.Prime] (F F₁ : IntermediateField ℚ (AlgebraicClosure ℚ))
  [NumberField ↥F] [IsGalois ℚ ↥F] [NumberField ↥F₁] [IsGalois ℚ ↥F₁] [hle : Fact (F ≤ F₁)] (hp2 : p ≠ 2)

example := invinfl_sys F F₁ hp2 (InvSys.stdp p hp2 F₁) (InvSys.stdp_iii' p hp2 F₁)

end check
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

end Reduce95
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

set_option autoImplicit false
open CategoryTheory

attribute [scoped instance 10] AddCommGroup.toIntModule

namespace Reduce95
namespace Infl

variable {G G₁ : Type} [Group G] [Group G₁] (π : G₁ →* G) (B : Rep ℤ G)

noncomputable def inflHom {X : Rep ℤ G} {X₁ : Rep ℤ G₁} (jX : Rep.res π X ⟶ X₁) :
    (Rep.relationModuleInt B ⟶ X) →+ (Rep.relationModuleInt (Rep.res π B) ⟶ X₁) :=
  AddMonoidHom.mk' (fun t => Rep.relationModuleInt.resMap π B ≫ (Rep.resFunctor π).map t ≫ jX) (fun t t' => by
    have hadd : (Rep.resFunctor π).map (t + t') = (Rep.resFunctor π).map t + (Rep.resFunctor π).map t' :=
      Rep.hom_ext (DFunLike.ext _ _ fun _ => rfl)
    beta_reduce
    rw [hadd, Preadditive.add_comp, Preadditive.comp_add])

theorem inflHom_apply {X : Rep ℤ G} {X₁ : Rep ℤ G₁} (jX : Rep.res π X ⟶ X₁) (t : Rep.relationModuleInt B ⟶ X) :
    inflHom π B jX t = Rep.relationModuleInt.resMap π B ≫ (Rep.resFunctor π).map t ≫ jX := rfl

theorem inflHom_comp_of_sq {X X' : Rep ℤ G} {X₁ X₁' : Rep ℤ G₁} (jX : Rep.res π X ⟶ X₁) (jX' : Rep.res π X' ⟶ X₁')
    (u : X ⟶ X') (u₁ : X₁ ⟶ X₁') (hsq : (Rep.resFunctor π).map u ≫ jX' = jX ≫ u₁) (t : Rep.relationModuleInt B ⟶ X) :
    inflHom π B jX' (t ≫ u) = inflHom π B jX t ≫ u₁ := by
  rw [inflHom_apply, inflHom_apply, Functor.map_comp]
  simp only [Category.assoc]
  rw [hsq]

theorem inflHom_comp_right {X : Rep ℤ G} {X₁ X₁' : Rep ℤ G₁} (jX : Rep.res π X ⟶ X₁) (v : X₁ ⟶ X₁')
    (t : Rep.relationModuleInt B ⟶ X) : inflHom π B (jX ≫ v) t = inflHom π B jX t ≫ v := by
  rw [inflHom_apply, inflHom_apply]
  simp only [Category.assoc]

theorem inflHom_ι_comp {X : Rep ℤ G} {X₁ : Rep ℤ G₁} (jX : Rep.res π X ⟶ X₁) (χ : Rep.free ℤ G B ⟶ X) :
    inflHom π B jX (Rep.relationModuleInt.ι B ≫ χ) =
      Rep.relationModuleInt.ι (Rep.res π B) ≫ (Rep.freeResMap π B ≫ (Rep.resFunctor π).map χ ≫ jX) := by
  have hsqι : Rep.relationModuleInt.resMap π B ≫ (Rep.resFunctor π).map (Rep.relationModuleInt.ι B) =
      Rep.relationModuleInt.ι (Rep.res π B) ≫ Rep.freeResMap π B :=
    Rep.hom_ext (DFunLike.ext _ _ fun _ => rfl)
  rw [inflHom_apply, Functor.map_comp]
  have h := congrArg (· ≫ (Rep.resFunctor π).map χ ≫ jX) hsqι
  simp only [Category.assoc] at h ⊢
  exact h

noncomputable def inflH1 : groupCohomology B 1 →+ groupCohomology (Rep.res π B) 1 :=
  (groupCohomology.map π (𝟙 (Rep.res π B)) 1).hom.toAddMonoidHom

theorem inflH1_apply (x : groupCohomology B 1) : inflH1 π B x = (groupCohomology.map π (𝟙 (Rep.res π B)) 1).hom x := rfl

theorem surjective_of_forall_comp_eq_of_range_iff {VB VB₁ W : Type} [AddCommGroup VB] [AddCommGroup VB₁] [AddCommGroup W]
    (infl : VB →+ W) (infl₁ : VB₁ →+ W) (iB : VB →+ VB₁) (htri : ∀ x, infl₁ (iB x) = infl x)
    (P : W → Prop) (hrange : ∀ y, P y ↔ ∃ x, infl x = y) (hrange₁ : ∀ y, P y ↔ ∃ x₁, infl₁ x₁ = y)
    (hinj₁ : Function.Injective infl₁) : Function.Surjective iB := by
  intro x₁
  obtain ⟨x, hx⟩ := (hrange _).1 ((hrange₁ (infl₁ x₁)).2 ⟨x₁, rfl⟩)
  exact ⟨x, hinj₁ (by rw [htri, hx])⟩

theorem hiSlam {J C : Rep ℤ G} {J₁ C₁ : Rep ℤ G₁} (jJ : Rep.res π J ⟶ J₁) (jC : Rep.res π C ⟶ C₁) (lamJ : J ⟶ C) (lamJ₁ : J₁ ⟶ C₁)
    (hsq : (Rep.resFunctor π).map lamJ ≫ jC = jJ ≫ lamJ₁) (s : Rep.relationModuleInt B ⟶ J) :
    inflHom π B jC (s ≫ lamJ) = inflHom π B jJ s ≫ lamJ₁ :=
  inflHom_comp_of_sq π B jJ jC lamJ lamJ₁ hsq s

theorem hiSY {J Y : Rep ℤ G} {J₁ Y₁ : Rep ℤ G₁} (jJ : Rep.res π J ⟶ J₁) (jY : Rep.res π Y ⟶ Y₁) (gJY : J ⟶ Y) (gJY₁ : J₁ ⟶ Y₁)
    (hsq : (Rep.resFunctor π).map gJY ≫ jY = jJ ≫ gJY₁) (t : Rep.relationModuleInt B ⟶ J) :
    inflHom π B jY (t ≫ gJY) = inflHom π B jJ t ≫ gJY₁ :=
  inflHom_comp_of_sq π B jJ jY gJY gJY₁ hsq t

theorem inflHom_eq_resMap_comp {X : Rep ℤ G} {X₁ : Rep ℤ G₁} (jX : Rep.res π X ⟶ X₁) (t : Rep.relationModuleInt B ⟶ X) :
    inflHom π B jX t = Rep.relationModuleInt.resMap π B ≫ (Rep.resFunctor π).map t ≫ jX := rfl

theorem freeResMap_comp {G₂ : Type} [Group G₂] (π' : G₂ →* G₁) :
    Rep.freeResMap (π.comp π') B = Rep.freeResMap π' (Rep.res π B) ≫ (Rep.resFunctor π').map (Rep.freeResMap π B) :=
  Rep.free_ext ℤ G₂ _ _ _ (fun b => by
    rw [Rep.hom_comp, Representation.IntertwiningMap.comp_apply]
    erw [Rep.resMap_hom_apply]
    simp [Rep.freeResMap])

theorem resMap_comp {G₂ : Type} [Group G₂] (π' : G₂ →* G₁) :
    Rep.relationModuleInt.resMap (π.comp π') B =
      Rep.relationModuleInt.resMap π' (Rep.res π B) ≫ (Rep.resFunctor π').map (Rep.relationModuleInt.resMap π B) := by
  refine Rep.hom_ext (DFunLike.ext _ _ fun x => Subtype.ext ?_)
  change (Rep.freeResMap (π.comp π') B).hom _ = (Rep.freeResMap π B).hom ((Rep.freeResMap π' (Rep.res π B)).hom _)
  rw [freeResMap_comp]
  rfl

theorem inflHom_comp_inflHom {G₂ : Type} [Group G₂] (π' : G₂ →* G₁) {X : Rep ℤ G} {X₁ : Rep ℤ G₁} {X₂ : Rep ℤ G₂}
    (jX : Rep.res π X ⟶ X₁) (jX' : Rep.res π' X₁ ⟶ X₂) (t : Rep.relationModuleInt B ⟶ X) :
    inflHom π' (Rep.res π B) jX' (inflHom π B jX t) =
      inflHom (π.comp π') B ((Rep.resFunctor π').map jX ≫ jX' : Rep.res (π.comp π') X ⟶ X₂) t := by
  rw [inflHom_apply, inflHom_apply, inflHom_apply, resMap_comp]
  simp only [Category.assoc]
  rfl

noncomputable abbrev inflIhom {X : Rep ℤ G} {X₁ : Rep ℤ G₁} (jX : Rep.res π X ⟶ X₁) :
    Rep.res π ((ihom (Rep.relationModuleInt B)).obj X) ⟶ (ihom (Rep.relationModuleInt (Rep.res π B))).obj X₁ :=
  Rep.extInflR π B X X₁ jX

theorem inflIhom_eq_extInflR {X : Rep ℤ G} {X₁ : Rep ℤ G₁} (jX : Rep.res π X ⟶ X₁) : inflIhom π B jX = Rep.extInflR π B X X₁ jX := rfl

theorem inflIhom_hom_apply {X : Rep ℤ G} {X₁ : Rep ℤ G₁} (jX : Rep.res π X ⟶ X₁)
    (f : Rep.res π ((ihom (Rep.relationModuleInt B)).obj X)) (x : Rep.relationModuleInt (Rep.res π B)) :
    LinearMap.toAddMonoidHom ((inflIhom π B jX).hom f) x = jX.hom (LinearMap.toAddMonoidHom f ((Rep.relationModuleInt.resMap π B).hom x)) :=
  rfl

noncomputable def inflExt1 {X : Rep ℤ G} {X₁ : Rep ℤ G₁} (jX : Rep.res π X ⟶ X₁) :
    groupCohomology ((ihom (Rep.relationModuleInt B)).obj X) 1 →+ groupCohomology ((ihom (Rep.relationModuleInt (Rep.res π B))).obj X₁) 1 :=
  (groupCohomology.map π (inflIhom π B jX) 1).hom.toAddMonoidHom

theorem inflExt1_apply {X : Rep ℤ G} {X₁ : Rep ℤ G₁} (jX : Rep.res π X ⟶ X₁) (y : groupCohomology ((ihom (Rep.relationModuleInt B)).obj X) 1) :
    inflExt1 π B jX y = (groupCohomology.map π (inflIhom π B jX) 1).hom y := rfl

theorem inflExt1_H1π {X : Rep ℤ G} {X₁ : Rep ℤ G₁} (jX : Rep.res π X ⟶ X₁) (a : groupCohomology.cocycles₁ ((ihom (Rep.relationModuleInt B)).obj X)) :
    inflExt1 π B jX ((groupCohomology.H1π _).hom a) = (groupCohomology.H1π _).hom (groupCohomology.mapCocycles₁ π (inflIhom π B jX) a) := by
  rw [inflExt1_apply]
  exact groupCohomology.H1π_comp_map_apply π (inflIhom π B jX) a

theorem inflIhom_comp_inflIhom {G₂ : Type} [Group G₂] (π' : G₂ →* G₁) {X : Rep ℤ G} {X₁ : Rep ℤ G₁} {X₂ : Rep ℤ G₂}
    (jX : Rep.res π X ⟶ X₁) (jX' : Rep.res π' X₁ ⟶ X₂) :
    (Rep.resFunctor π').map (inflIhom π B jX) ≫ inflIhom π' (Rep.res π B) jX' =
      (inflIhom (π.comp π') B ((Rep.resFunctor π').map jX ≫ jX') :
        Rep.res (π.comp π') ((ihom (Rep.relationModuleInt B)).obj X) ⟶ (ihom (Rep.relationModuleInt (Rep.res (π.comp π') B))).obj X₂) := by
  refine Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun f => LinearMap.ext fun x => ?_))
  change jX'.hom (jX.hom (LinearMap.toAddMonoidHom f ((Rep.relationModuleInt.resMap π B).hom ((Rep.relationModuleInt.resMap π' (Rep.res π B)).hom x)))) =
    jX'.hom (jX.hom (LinearMap.toAddMonoidHom f ((Rep.relationModuleInt.resMap (π.comp π') B).hom x)))
  rw [resMap_comp π B π']
  rfl

theorem inflExt1_inflExt1 {G₂ : Type} [Group G₂] (π' : G₂ →* G₁) {X : Rep ℤ G} {X₁ : Rep ℤ G₁} {X₂ : Rep ℤ G₂}
    (jX : Rep.res π X ⟶ X₁) (jX' : Rep.res π' X₁ ⟶ X₂) (y : groupCohomology ((ihom (Rep.relationModuleInt B)).obj X) 1) :
    inflExt1 π' (Rep.res π B) jX' (inflExt1 π B jX y) =
      inflExt1 (π.comp π') B ((Rep.resFunctor π').map jX ≫ jX' : Rep.res (π.comp π') X ⟶ X₂) y := by
  rw [inflExt1_apply, inflExt1_apply, inflExt1_apply, ← ModuleCat.comp_apply, ← groupCohomology.map_comp,
    inflIhom_comp_inflIhom]

theorem mapCocycles₁_inflIhom_apply {X : Rep ℤ G} {X₁ : Rep ℤ G₁} (jX : Rep.res π X ⟶ X₁)
    (a : groupCohomology.cocycles₁ ((ihom (Rep.relationModuleInt B)).obj X)) (d' : G₁) (x' : Rep.relationModuleInt (Rep.res π B)) :
    LinearMap.toAddMonoidHom ((groupCohomology.mapCocycles₁ π (inflIhom π B jX) a : G₁ → _) d') x' =
      jX.hom (LinearMap.toAddMonoidHom ((a : G → _) (π d')) ((Rep.relationModuleInt.resMap π B).hom x')) := by
  rfl

theorem inflIhom_sq {X X' : Rep ℤ G} {X₁ X₁' : Rep ℤ G₁} (jX : Rep.res π X ⟶ X₁) (jX' : Rep.res π X' ⟶ X₁')
    (u : X ⟶ X') (u₁ : X₁ ⟶ X₁') (hsq : (Rep.resFunctor π).map u ≫ jX' = jX ≫ u₁) :
    (Rep.resFunctor π).map ((ihom (Rep.relationModuleInt B)).map u) ≫ inflIhom π B jX' =
      inflIhom π B jX ≫ (ihom (Rep.relationModuleInt (Rep.res π B))).map u₁ := by
  refine Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun f => LinearMap.ext fun x => ?_))
  exact congrArg (fun φ => φ.hom (LinearMap.toAddMonoidHom f ((Rep.relationModuleInt.resMap π B).hom x))) hsq

theorem map_δ_inflIhom {T : ShortComplex (Rep ℤ G)} {T₁ : ShortComplex (Rep ℤ G₁)}
    (hT : (T.map (ihom (Rep.relationModuleInt B))).ShortExact) (hT₁ : (T₁.map (ihom (Rep.relationModuleInt (Rep.res π B)))).ShortExact)
    (jE : Rep.res π T.X₁ ⟶ T₁.X₁) (jJ : Rep.res π T.X₂ ⟶ T₁.X₂) (jY : Rep.res π T.X₃ ⟶ T₁.X₃)
    (hsqf : (Rep.resFunctor π).map T.f ≫ jJ = jE ≫ T₁.f) (hsqg : (Rep.resFunctor π).map T.g ≫ jY = jJ ≫ T₁.g)
    (i j : ℕ) (hij : i + 1 = j) (y : groupCohomology ((ihom (Rep.relationModuleInt B)).obj T.X₃) i) :
    (groupCohomology.map π (inflIhom π B jE) j).hom ((groupCohomology.δ hT i j hij).hom y) =
      (groupCohomology.δ hT₁ i j hij).hom ((groupCohomology.map π (inflIhom π B jY) i).hom y) :=
  groupCohomology.map_delta_eq_delta_map π hT hT₁ (inflIhom π B jE) (inflIhom π B jJ) (inflIhom π B jY)
    (inflIhom_sq π B jE jJ T.f T₁.f hsqf) (inflIhom_sq π B jJ jY T.g T₁.g hsqg) i j hij y

theorem inflH1_H1π (n : groupCohomology.cocycles₁ B) :
    inflH1 π B ((groupCohomology.H1π B).hom n) = (groupCohomology.H1π (Rep.res π B)).hom (groupCohomology.mapCocycles₁ π (𝟙 (Rep.res π B)) n) := by
  rw [inflH1_apply]
  exact groupCohomology.H1π_comp_map_apply π (𝟙 (Rep.res π B)) n

theorem mapCocycles₁_id_apply (n : groupCohomology.cocycles₁ B) (d' : G₁) :
    (groupCohomology.mapCocycles₁ π (𝟙 (Rep.res π B)) n : G₁ → _) d' = (n : G → B) (π d') := rfl

theorem inflH1_inflH1 {G₂ : Type} [Group G₂] (π' : G₂ →* G₁) (x : groupCohomology B 1) :
    inflH1 π' (Rep.res π B) (inflH1 π B x) = inflH1 (π.comp π') B x := by
  rw [inflH1_apply, inflH1_apply, inflH1_apply, ← ModuleCat.comp_apply, ← groupCohomology.map_comp]
  rfl

def readCocycle {Γ : Type} [Group Γ] (r : Γ →* G) {k : Type} [CommRing k] {W : Rep k Γ} (β : B →+ W)
    (hβeq : ∀ (γ : Γ) (b : B), β (B.ρ (r γ) b) = W.ρ γ (β b)) (n : groupCohomology.cocycles₁ B) : groupCohomology.cocycles₁ W :=
  ⟨fun γ => β (n (r γ)), (groupCohomology.mem_cocycles₁_iff _).2 fun g h => by
    have hn := (groupCohomology.mem_cocycles₁_iff (n : G → B)).1 n.2 (r g) (r h)
    simp only [map_mul, hn, map_add, hβeq]⟩

theorem readCocycle_apply {Γ : Type} [Group Γ] (r : Γ →* G) {k : Type} [CommRing k] {W : Rep k Γ} (β : B →+ W)
    (hβeq : ∀ (γ : Γ) (b : B), β (B.ρ (r γ) b) = W.ρ γ (β b)) (n : groupCohomology.cocycles₁ B) (γ : Γ) :
    readCocycle B r β hβeq n γ = β (n (r γ)) := rfl

theorem infl_inflH1_eq {Γ : Type} [Group Γ] (r : Γ →* G) (r₁ : Γ →* G₁) (hπ : ∀ γ, π (r₁ γ) = r γ)
    {k : Type} [CommRing k] {W : Rep k Γ} {VW : Type} [AddCommGroup VW] (cls : groupCohomology.cocycles₁ W → VW) (β : B →+ W)
    (hβeq : ∀ (γ : Γ) (b : B), β (B.ρ (r γ) b) = W.ρ γ (β b))
    (infl : groupCohomology B 1 →+ VW) (infl₁ : groupCohomology (Rep.res π B) 1 →+ VW)
    (hinflpin : ∀ (n : groupCohomology.cocycles₁ B) (ny : groupCohomology.cocycles₁ W),
      (∀ γ, ny γ = β (n (r γ))) → infl ((groupCohomology.H1π B).hom n) = cls ny)
    (hinflpin₁ : ∀ (n : groupCohomology.cocycles₁ (Rep.res π B)) (ny : groupCohomology.cocycles₁ W),
      (∀ γ, ny γ = β (n (r₁ γ))) → infl₁ ((groupCohomology.H1π (Rep.res π B)).hom n) = cls ny)
    (x : groupCohomology B 1) : infl₁ (inflH1 π B x) = infl x := by
  induction x using groupCohomology.H1_induction_on with
  | h n =>
    rw [hinflpin n (readCocycle B r β hβeq n) (fun γ => rfl), inflH1_H1π,
      hinflpin₁ _ (readCocycle B r β hβeq n) (fun γ => by rw [mapCocycles₁_id_apply, hπ]; rfl)]

theorem resMap_comp_ι :
    Rep.relationModuleInt.resMap π B ≫ (Rep.resFunctor π).map (Rep.relationModuleInt.ι B) =
      Rep.relationModuleInt.ι (Rep.res π B) ≫ Rep.freeResMap π B :=
  Rep.hom_ext (DFunLike.ext _ _ fun _ => rfl)

theorem map_H0Iso_inv {k : Type} [CommRing k] {A : Rep k G} {A₁ : Rep k G₁} (φ : Rep.res π A ⟶ A₁)
    (z : A.ρ.invariants) (z₁ : A₁.ρ.invariants) (h : (z₁ : A₁) = φ.hom (z : A)) :
    (groupCohomology.map π φ 0).hom ((groupCohomology.H0Iso A).inv z) = (groupCohomology.H0Iso A₁).inv z₁ := by
  apply (groupCohomology.H0Iso A₁).toLinearEquiv.injective
  change (groupCohomology.H0Iso A₁).hom _ = (groupCohomology.H0Iso A₁).hom _
  rw [Iso.inv_hom_id_apply]
  apply Subtype.ext
  rw [h]
  have := groupCohomology.map_H0Iso_hom_f_apply π φ ((groupCohomology.H0Iso A).inv z)
  rw [Iso.inv_hom_id_apply] at this
  exact this

end Infl
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"
end Reduce95
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

namespace Reduce95
namespace Infl
open ExtCitation groupCohomology GroupCohomology M4aHerbrand IsDedekindDomain NumberField

section level

variable {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
  (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) [FiniteDimensional (ZMod p) M]
  (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p)
  (F F₁ : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F] [NumberField ↥F₁] [IsGalois ℚ ↥F₁]
  (hle : F ≤ F₁) (hFS : F.IsUnramifiedOutside S) (hF₁S : F₁.IsUnramifiedOutside S)
  (hunr : ∀ w : HeightOneSpectrum (𝓞 ↥F), w ∉ TT S F → Ideal.ramificationIdx' (w.asIdeal.under (𝓞 ℚ)) w.asIdeal = 1)
  (hunr₁ : ∀ w : HeightOneSpectrum (𝓞 ↥F₁), w ∉ TT S F₁ → Ideal.ramificationIdx' (w.asIdeal.under (𝓞 ℚ)) w.asIdeal = 1)

  (π : (↥F₁ ≃ₐ[ℚ] ↥F₁) →* (↥F ≃ₐ[ℚ] ↥F))
  (hπ : ∀ γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, π (AlgEquiv.restrictNormalHom ↥F₁ γ) = AlgEquiv.restrictNormalHom ↥F γ)

  (B : Rep ℤ (↥F ≃ₐ[ℚ] ↥F)) [Fintype B] (β : B →+ M.dualTwist (cycloChar p))
  (hβeq : ∀ (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (b : B),
    β (B.ρ (AlgEquiv.restrictNormalHom ↥F γ) b) = (M.dualTwist (cycloChar p)).ρ γ (β b))
  (hβ : Function.Bijective β) (hB : ∀ b : B, p • b = 0)

  (jE : Rep.res π (seqF S F).X₁ ⟶ (seqF S F₁).X₁)
  (jJ : Rep.res π (seqF S F).X₂ ⟶ (seqF S F₁).X₂)
  (jY : Rep.res π (seqF S F).X₃ ⟶ (seqF S F₁).X₃)
  (jC : Rep.res π (CS S F) ⟶ CS S F₁)
  (hsqE : (Rep.resFunctor π).map (seqF S F).f ≫ jJ = jE ≫ (seqF S F₁).f)
  (hsqY : (Rep.resFunctor π).map (seqF S F).g ≫ jY = jJ ≫ (seqF S F₁).g)
  (hsqC : (Rep.resFunctor π).map (RepImage.ι (LF S F)) ≫ jC = jY ≫ RepImage.ι (LF S F₁))
  (hjE : ∀ x, iotaE F₁ (Sq S) (jE.hom x) = iotaE F (Sq S) x)

scoped instance fintypeRes : Fintype (Rep.res π B) := ‹Fintype B›

include hπ hβeq in
omit [FiniteDimensional (ZMod p) M] [NumberField ↥F] [NumberField ↥F₁] [Fintype B] in

theorem hβeq_res : ∀ (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (b : Rep.res π B),
    β ((Rep.res π B).ρ (AlgEquiv.restrictNormalHom ↥F₁ γ) b) = (M.dualTwist (cycloChar p)).ρ γ (β b) := by
  intro γ b
  change β (B.ρ (π (AlgEquiv.restrictNormalHom ↥F₁ γ)) b) = _
  rw [hπ]
  exact hβeq γ b

include hsqC in
omit [Fintype B] in

theorem hiCj (t : Rep.relationModuleInt B ⟶ (seqF S F).X₃) :
    inflHom π B jC (t ≫ RepImage.ι (LF S F)) = inflHom π B jY t ≫ RepImage.ι (LF S F₁) :=
  inflHom_comp_of_sq π B jY jC (RepImage.ι (LF S F)) (RepImage.ι (LF S F₁)) hsqC t

set_option maxHeartbeats 6400000 in
include hsqE hsqY in

theorem hid (t : Rep.relationModuleInt B ⟶ (seqF S F).X₃) :
    dY' S F₁ (Rep.res π B) (inflHom π B jY t) = inflExt1 π B jE (dY' S F B t) := by
  rw [dY'_apply, dY'_apply, inflExt1_apply, map_δ_inflIhom π B (hT' S F B) (hT' S F₁ (Rep.res π B)) jE jJ jY hsqE hsqY 0 1 rfl]
  congr 1
  symm
  apply map_H0Iso_inv
  rfl

set_option maxHeartbeats 6400000 in
include hle hπ hjE in

theorem hiL (x : H1 ((ihom (Rep.relationModuleInt B)).obj (seqF S F).X₁)) :
    LE2' S hpS M ζ hζ F₁ hF₁S (Rep.res π B) β (hβeq_res M F F₁ π hπ B β hβeq) hβ hB (inflExt1 π B jE x) =
      LE2' S hpS M ζ hζ F hFS B β hβeq hβ hB x := by
  haveI : Fintype (↥F ≃ₐ[ℚ] ↥F) := Fintype.ofFinite _
  haveI : Fintype (↥F₁ ≃ₐ[ℚ] ↥F₁) := Fintype.ofFinite _
  induction x using groupCohomology.H1_induction_on with
  | h a =>
    rw [inflExt1_H1π]
    exact NumberField.SUnits.isGlobalBridge2_apply_inflation_eq S hpS (Sq S) (coe_Sq S) M F F₁ hle hFS hF₁S π hπ
      (Rep.relationModuleInt.ι B) (Rep.freeCover B) (relationModuleInt_ι_injective B) (exact_ι_freeCover B) (freeCover_surjective B)
      (Rep.relationModuleInt.ι (Rep.res π B)) (Rep.freeCover (Rep.res π B))
      (relationModuleInt_ι_injective (Rep.res π B)) (exact_ι_freeCover (Rep.res π B)) (freeCover_surjective (Rep.res π B))
      hB (Rep.relationModuleInt.resMap π B) (Rep.freeResMap π B)
      (resMap_comp_ι π B).symm (Rep.freeResMap_comp_resFunctor_map_freeCover π B).symm
      (iotaE F (Sq S)) (toMul_iotaE F (Sq S)) (iotaE F₁ (Sq S)) (toMul_iotaE F₁ (Sq S)) jE hjE
      (kappa M ζ hζ B β) (kappa_equivariant M ζ hζ (AlgEquiv.restrictNormalHom ↥F) B β hβeq) (kappa_perfect M ζ hζ B β hβ hB)
      (LE2'_spec S hpS M ζ hζ F hFS B β hβeq hβ hB)
      (LE2'_spec S hpS M ζ hζ F₁ hF₁S (Rep.res π B) β (hβeq_res M F F₁ π hπ B β hβeq) hβ hB)
      a (groupCohomology.mapCocycles₁ π (inflIhom π B jE) a) (mapCocycles₁_inflIhom_apply π B jE a)

omit [FiniteDimensional (ZMod p) M] in

theorem hial_of_hal
    (al : (Rep.relationModuleInt B ⟶ CS S F) →+ (groupCohomology B 1 →+ ZMod p))
    (al₁ : (Rep.relationModuleInt (Rep.res π B) ⟶ CS S F₁) →+ (groupCohomology (Rep.res π B) 1 →+ ZMod p))
    (inv : groupCohomology (CS S F) 2 →+ AddCircle (1 : ℚ)) (inv₁ : groupCohomology (CS S F₁) 2 →+ AddCircle (1 : ℚ))
    (hal : ∀ (φ : Rep.relationModuleInt B ⟶ CS S F) (y : groupCohomology B 1),
      inv ((groupCohomology.map (MonoidHom.id _) φ 2).hom ((groupCohomology.δ (hX' F B) 1 2 rfl).hom y)) =
        ((((al φ y).val : ℚ) / (p : ℚ) : ℚ) : AddCircle (1 : ℚ)))
    (hal₁ : ∀ (φ₁ : Rep.relationModuleInt (Rep.res π B) ⟶ CS S F₁) (y₁ : groupCohomology (Rep.res π B) 1),
      inv₁ ((groupCohomology.map (MonoidHom.id _) φ₁ 2).hom ((groupCohomology.δ (hX' F₁ (Rep.res π B)) 1 2 rfl).hom y₁)) =
        ((((al₁ φ₁ y₁).val : ℚ) / (p : ℚ) : ℚ) : AddCircle (1 : ℚ)))
    (hjCinv : ∀ c : groupCohomology (CS S F) 2, inv₁ ((groupCohomology.map π jC 2).hom c) = inv c)
    (φ : Rep.relationModuleInt B ⟶ CS S F) (x : groupCohomology B 1) :
    al₁ (inflHom π B jC φ) (inflH1 π B x) = al φ x := by
  haveI : Fintype (↥F ≃ₐ[ℚ] ↥F) := Fintype.ofFinite _
  haveI : Fintype (↥F₁ ≃ₐ[ℚ] ↥F₁) := Fintype.ofFinite _
  apply ep_injective p
  rw [ep_apply, ep_apply, ← hal, ← hal₁, inflHom_apply, inflH1_apply]
  exact (congrArg inv₁
    (Rep.map_delta_resMap_comp_eq_map_map_delta π (CS S F) (CS S F₁) jC B (hX' F B) (hX' F₁ (Rep.res π B)) φ x)).trans (hjCinv _)

include hπ hβeq in
omit [FiniteDimensional (ZMod p) M] [NumberField ↥F] [NumberField ↥F₁] [Fintype B] in

theorem infl_inflH1 (infl : groupCohomology B 1 →+ H1 (M.dualTwist (cycloChar p)))
    (infl₁ : groupCohomology (Rep.res π B) 1 →+ H1 (M.dualTwist (cycloChar p)))
    (hinflpin : ∀ (n : cocycles₁ B) (ny : cocycles₁ (M.dualTwist (cycloChar p))),
      (∀ γ, ny γ = β (n (AlgEquiv.restrictNormalHom ↥F γ))) → infl ((H1π B).hom n) = (H1π (M.dualTwist (cycloChar p))).hom ny)
    (hinflpin₁ : ∀ (n : cocycles₁ (Rep.res π B)) (ny : cocycles₁ (M.dualTwist (cycloChar p))),
      (∀ γ, ny γ = β (n (AlgEquiv.restrictNormalHom ↥F₁ γ))) → infl₁ ((H1π (Rep.res π B)).hom n) = (H1π (M.dualTwist (cycloChar p))).hom ny)
    (x : groupCohomology B 1) : infl₁ (inflH1 π B x) = infl x :=
  infl_inflH1_eq π B (AlgEquiv.restrictNormalHom ↥F) (AlgEquiv.restrictNormalHom ↥F₁) hπ
    (fun ny => (H1π (M.dualTwist (cycloChar p))).hom ny) β hβeq infl infl₁ hinflpin hinflpin₁ x

include hπ hβeq in
omit [FiniteDimensional (ZMod p) M] [NumberField ↥F] [NumberField ↥F₁] [Fintype B] in

theorem inflH1_surjective (infl : groupCohomology B 1 →+ H1 (M.dualTwist (cycloChar p)))
    (infl₁ : groupCohomology (Rep.res π B) 1 →+ H1 (M.dualTwist (cycloChar p)))
    (hinflpin : ∀ (n : cocycles₁ B) (ny : cocycles₁ (M.dualTwist (cycloChar p))),
      (∀ γ, ny γ = β (n (AlgEquiv.restrictNormalHom ↥F γ))) → infl ((H1π B).hom n) = (H1π (M.dualTwist (cycloChar p))).hom ny)
    (hinflpin₁ : ∀ (n : cocycles₁ (Rep.res π B)) (ny : cocycles₁ (M.dualTwist (cycloChar p))),
      (∀ γ, ny γ = β (n (AlgEquiv.restrictNormalHom ↥F₁ γ))) → infl₁ ((H1π (Rep.res π B)).hom n) = (H1π (M.dualTwist (cycloChar p))).hom ny)
    (hrange : ∀ y : H1 (M.dualTwist (cycloChar p)), y ∈ continuousH1S S (M.dualTwist (cycloChar p)) ↔ ∃ x, infl x = y)
    (hrange₁ : ∀ y : H1 (M.dualTwist (cycloChar p)), y ∈ continuousH1S S (M.dualTwist (cycloChar p)) ↔ ∃ x₁, infl₁ x₁ = y)
    (hinj₁ : Function.Injective infl₁) : Function.Surjective (inflH1 π B) :=
  surjective_of_forall_comp_eq_of_range_iff infl infl₁ (inflH1 π B)
    (infl_inflH1 M F F₁ π hπ B β hβeq infl infl₁ hinflpin hinflpin₁) _ hrange hrange₁ hinj₁

include hle hF₁S in
omit [FiniteDimensional (ZMod p) M] [NumberField ↥F] [IsGalois ℚ ↥F] [NumberField ↥F₁] [IsGalois ℚ ↥F₁] [Fintype B] in

theorem hrange_of_le (infl₁ : groupCohomology (Rep.res π B) 1 →+ H1 (M.dualTwist (cycloChar p)))
    (hinflrange₁ : ∀ y : H1 (M.dualTwist (cycloChar p)), (∃ x, infl₁ x = y) ↔
      ∃ ny : cocycles₁ (M.dualTwist (cycloChar p)), (H1π (M.dualTwist (cycloChar p))).hom ny = y ∧
        (∀ (γ s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), s ∈ F₁.fixingSubgroup → ny (γ * s) = ny γ) ∧
        (∀ s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, s ∈ F₁.fixingSubgroup → ny s = 0))
    (hSTAB1 : ∀ y : H1 (M.dualTwist (cycloChar p)), y ∈ continuousH1S S (M.dualTwist (cycloChar p)) →
      ∃ ny : cocycles₁ (M.dualTwist (cycloChar p)), (H1π (M.dualTwist (cycloChar p))).hom ny = y ∧
        (∀ (γ s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), s ∈ F.fixingSubgroup → ny (γ * s) = ny γ) ∧
        (∀ s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, s ∈ F.fixingSubgroup → ny s = 0))
    (y : H1 (M.dualTwist (cycloChar p))) : y ∈ continuousH1S S (M.dualTwist (cycloChar p)) ↔ ∃ x₁, infl₁ x₁ = y := by
  have hsub : F₁.fixingSubgroup ≤ F.fixingSubgroup := fun s hs => by
    rw [IntermediateField.mem_fixingSubgroup_iff] at hs ⊢
    exact fun x hx => hs x (hle hx)
  constructor
  · intro hy
    obtain ⟨ny, hny, hconst, hzero⟩ := hSTAB1 y hy
    exact (hinflrange₁ y).2 ⟨ny, hny, fun γ s hs => hconst γ s (hsub hs), fun s hs => hzero s (hsub hs)⟩
  · intro hx
    obtain ⟨ny, hny, hconst, -⟩ := (hinflrange₁ y).1 hx
    rw [groupCohomology.mem_continuousH1S_iff]
    exact ⟨ny, ⟨F₁, hF₁S, fun γ s hs => hconst γ s hs⟩, hny⟩

end level
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95"

end Infl
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95 P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95.Infl"
end Reduce95
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95 P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95.Infl"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxSynthPendingDepth 3
open CategoryTheory IsDedekindDomain NumberField

namespace Reduce95
open ExtCitation groupCohomology GroupCohomology M4aHerbrand
open scoped NumberField.PlaceDecomp

section levels

variable {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
  (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) [FiniteDimensional (ZMod p) M]
  (hsm : ∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
    ∀ s ∈ F.fixingSubgroup, M.ρ s m = m)
  (hMur : ∀ q : Nat.Primes, q ∉ S → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
    A.LiesOverPrime (q : ℕ) → ∀ g ∈ A.inertiaSubgroupIn ℚ, M.ρ g = 1)
  (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p)

def SepClause (F F₁ : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F] [NumberField ↥F₁] [IsGalois ℚ ↥F₁]
    (B : Rep ℤ (↥F ≃ₐ[ℚ] ↥F)) : Prop :=
  ∀ (π : (↥F₁ ≃ₐ[ℚ] ↥F₁) →* (↥F ≃ₐ[ℚ] ↥F))
    (_ : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      π (AlgEquiv.restrictNormalHom ↥F₁ σ) = AlgEquiv.restrictNormalHom ↥F σ)
    (D' : IdeleGaloisDescent (𝓞 ↥F₁) ℚ ↥F₁) (hD' : D'.StabilizesUnitIdeles (NumberField.placesOverPrimes ↥F₁ (↑S : Set Nat.Primes)))
    [MulDistribMulAction (↥F₁ ≃ₐ[ℚ] ↥F₁) (SIdeleClassGroup (𝓞 ↥F₁) ↥F₁ (NumberField.placesOverPrimes ↥F₁ (↑S : Set Nat.Primes)))]
    (_ : ∀ (g : ↥F₁ ≃ₐ[ℚ] ↥F₁) (c : SIdeleClassGroup (𝓞 ↥F₁) ↥F₁ (NumberField.placesOverPrimes ↥F₁ (↑S : Set Nat.Primes))),
      g • c = D'.sClassAct hD' g c)
    (j : Rep.res π (Rep.ofMulDistribMulAction (↥F ≃ₐ[ℚ] ↥F)
          (SIdeleClassGroup (𝓞 ↥F) ↥F (NumberField.placesOverPrimes ↥F (↑S : Set Nat.Primes)))) ⟶
        Rep.ofMulDistribMulAction (↥F₁ ≃ₐ[ℚ] ↥F₁)
          (SIdeleClassGroup (𝓞 ↥F₁) ↥F₁ (NumberField.placesOverPrimes ↥F₁ (↑S : Set Nat.Primes))))
    (hX : (Rep.relationSeqInt (Rep.res π B)).ShortExact)
    (φ : Rep.relationModuleInt B ⟶ Rep.ofMulDistribMulAction (↥F ≃ₐ[ℚ] ↥F)
          (SIdeleClassGroup (𝓞 ↥F) ↥F (NumberField.placesOverPrimes ↥F (↑S : Set Nat.Primes)))),
    (∃ χ : Rep.free ℤ (↥F₁ ≃ₐ[ℚ] ↥F₁) (Rep.res π B) ⟶ Rep.ofMulDistribMulAction (↥F₁ ≃ₐ[ℚ] ↥F₁)
          (SIdeleClassGroup (𝓞 ↥F₁) ↥F₁ (NumberField.placesOverPrimes ↥F₁ (↑S : Set Nat.Primes))),
        Rep.relationModuleInt.ι (Rep.res π B) ≫ χ =
          Rep.relationModuleInt.resMap π B ≫ (Rep.resFunctor π).map φ ≫ j) ∨
    (∃ y : groupCohomology (Rep.res π B) 1,
        (groupCohomology.map (MonoidHom.id (↥F₁ ≃ₐ[ℚ] ↥F₁))
            (Rep.relationModuleInt.resMap π B ≫ (Rep.resFunctor π).map φ ≫ j) 2).hom
          ((groupCohomology.δ hX 1 2 rfl).hom y) ≠ 0)

def CapClause (F₁ F₂ : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F₁] [NumberField ↥F₂] : Prop :=
  ∀ (h₁₂' : F₁ ≤ F₂) (Ψ : FiniteAdeleRing (𝓞 ↥F₁) ↥F₁ →+* FiniteAdeleRing (𝓞 ↥F₂) ↥F₂) (_ : Continuous Ψ)
    (_ : ∀ a : ↥F₁, Ψ (algebraMap ↥F₁ (FiniteAdeleRing (𝓞 ↥F₁) ↥F₁) a) =
      algebraMap ↥F₂ (FiniteAdeleRing (𝓞 ↥F₂) ↥F₂) (IntermediateField.inclusion h₁₂' a))
    (x : (FiniteAdeleRing (𝓞 ↥F₁) ↥F₁)ˣ),
    (∃ k : ℕ, x ^ p ^ k ∈ (Units.map (algebraMap ↥F₁ (FiniteAdeleRing (𝓞 ↥F₁) ↥F₁) : ↥F₁ →* FiniteAdeleRing (𝓞 ↥F₁) ↥F₁)).range ⊔
        IsDedekindDomain.FiniteAdeleRing.unitIdelesOutside (𝓞 ↥F₁) ↥F₁ (NumberField.placesOverPrimes ↥F₁ (↑S : Set Nat.Primes))) →
    Units.map (Ψ : FiniteAdeleRing (𝓞 ↥F₁) ↥F₁ →* FiniteAdeleRing (𝓞 ↥F₂) ↥F₂) x ∈
      (Units.map (algebraMap ↥F₂ (FiniteAdeleRing (𝓞 ↥F₂) ↥F₂) : ↥F₂ →* FiniteAdeleRing (𝓞 ↥F₂) ↥F₂)).range ⊔
        IsDedekindDomain.FiniteAdeleRing.unitIdelesOutside (𝓞 ↥F₂) ↥F₂ (NumberField.placesOverPrimes ↥F₂ (↑S : Set Nat.Primes))

include hpS hsm hMur hζ in

theorem exists_levels_exarch :
    ∃ (F F₁ F₂ : IntermediateField ℚ (AlgebraicClosure ℚ))
      (_ : NumberField ↥F) (_ : IsGalois ℚ ↥F) (_ : NumberField ↥F₁) (_ : IsGalois ℚ ↥F₁) (_ : NumberField ↥F₂) (_ : IsGalois ℚ ↥F₂),
      F ≤ F₁ ∧ F₁ ≤ F₂ ∧ F.IsUnramifiedOutside S ∧ F₁.IsUnramifiedOutside S ∧ F₂.IsUnramifiedOutside S ∧
      (∀ s ∈ F.fixingSubgroup, ∀ m : M.dualTwist (cycloChar p), (M.dualTwist (cycloChar p)).ρ s m = m) ∧
      (∀ x : H1 (M.dualTwist (cycloChar p)), x ∈ continuousH1S S (M.dualTwist (cycloChar p)) →
        ∃ ny : cocycles₁ (M.dualTwist (cycloChar p)), (H1π (M.dualTwist (cycloChar p))).hom ny = x ∧
          (∀ (γ s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), s ∈ F.fixingSubgroup → ny (γ * s) = ny γ) ∧
          (∀ s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, s ∈ F.fixingSubgroup → ny s = 0)) ∧
      ζ ∈ F ∧ p ∣ Nat.card (↥F ≃ₐ[ℚ] ↥F) ∧
      SepClause S F F₁ (Bof M F) ∧ CapClause (p := p) S F₁ F₂ := by
  haveI : FiniteDimensional (ZMod p) ↥(continuousH1S S (M.dualTwist (cycloChar p))) :=
    groupCohomology.finiteDimensional_continuousH1S S (M.dualTwist (cycloChar p)) (Rep.dualTwist_cycloChar_smooth M hsm)

  obtain ⟨F, instNF, instG, hFS, -, hFM', -, hSTAB1, hζF, hpG⟩ :=
    exists_baseLevel S hpS M hsm hMur ζ hζ (IntermediateField.adjoin ℚ {ζ}) (adjoin_prim_isUnramifiedOutside S hpS ζ hζ)

  obtain ⟨F₁, h₁, instNF₁, instG₁, hF₁S, hsep⟩ :=
    M4aHerbrand.exists_level_forall_relationHom_sIdeleClassGroup_extends_or_map_delta_ne_zero S hpS F hFS
      (DD F) (DD_stab S F) (fun _ _ => rfl) (Bof M F) (Bof_torsion M F)

  obtain ⟨F₂, h₁₂, instNF₂, hF₂S, instG₂, hcap⟩ :=
    NumberField.exists_le_isGalois_forall_mem_range_sup_unitIdelesOutside_of_pow_mem S hpS F₁ hF₁S
  exact ⟨F, F₁, F₂, instNF, instG, instNF₁, instG₁, instNF₂, instG₂, h₁, h₁₂, hFS, hF₁S, hF₂S, hFM', hSTAB1, hζF, hpG,
    fun π hπ D' hD' _ hact' j hX φ => hsep π hπ D' hD' hact' j hX φ, fun _ => hcap⟩

end levels
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95 P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95.Infl"

section hexf

variable {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes)
  (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) [FiniteDimensional (ZMod p) M]
  (F F₁ : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F] [NumberField ↥F₁] [IsGalois ℚ ↥F₁]
  (hunr₁ : ∀ w : HeightOneSpectrum (𝓞 ↥F₁), w ∉ TT S F₁ → Ideal.ramificationIdx' (w.asIdeal.under (𝓞 ℚ)) w.asIdeal = 1)
  (sys₁ : InvSys F₁)
  (π₁ : (↥F₁ ≃ₐ[ℚ] ↥F₁) →* (↥F ≃ₐ[ℚ] ↥F))
  (hπ₁ : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, π₁ (AlgEquiv.restrictNormalHom ↥F₁ σ) = AlgEquiv.restrictNormalHom ↥F σ)
  (jC₁ : Rep.res π₁ (CS S F) ⟶ CS S F₁)
  (hsep : SepClause S F F₁ (Bof M F))
  (u : ℕ) (hu : ∀ a : ZMod p, u • a = 0 → a = 0)

include hπ₁ hsep hu in

theorem hEXF_of_sep (φ : Rep.relationModuleInt (Bof M F) ⟶ CS S F) :
    (∃ χ : Rep.free ℤ (↥F₁ ≃ₐ[ℚ] ↥F₁) (Bofπ F M π₁) ⟶ CS S F₁,
        Infl.inflHom π₁ (Bof M F) jC₁ φ = Rep.relationModuleInt.ι (Bofπ F M π₁) ≫ χ) ∨
    (∃ x : ↥(groupCohomology (Bofπ F M π₁) 1),
        (u • alFs S F₁ hunr₁ sys₁ (Bofπ F M π₁) (Bofπ_torsion F M π₁)) (Infl.inflHom π₁ (Bof M F) jC₁ φ) x ≠ 0) := by
  rcases hsep π₁ hπ₁ (DD F₁) (DD_stab S F₁) (fun _ _ => rfl) jC₁ (hX' F₁ (Bofπ F M π₁)) φ with ⟨χ, hχ⟩ | ⟨y, hy⟩
  · exact Or.inl ⟨χ, hχ.symm⟩
  · refine Or.inr ⟨y, fun h0 => hy ?_⟩
    have h1 : alFs S F₁ hunr₁ sys₁ (Bofπ F M π₁) (Bofπ_torsion F M π₁) (Infl.inflHom π₁ (Bof M F) jC₁ φ) y = 0 := hu _ h0
    exact (alFs_eq_zero_iff S F₁ hunr₁ sys₁ (Bofπ F M π₁) (Bofπ_torsion F M π₁) _ y).1 h1

end hexf
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95 P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95.Infl"

end Reduce95
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95 P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95.Infl"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxSynthPendingDepth 3
open CategoryTheory IsDedekindDomain NumberField

namespace Reduce95
open ExtCitation groupCohomology GroupCohomology M4aHerbrand
open scoped NumberField.PlaceDecomp NumberField.PlaceTransport

section fincoker

variable (S : Finset Nat.Primes) (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F]

theorem toMul_PhiF_mem_unitIdelesTrivialOn (x : NumberField.SIdele.obj ℚ ↥F (Sq S))
    (hS : ∀ v : {v // v ∈ Sq S}, x (Sum.inl (Sum.inl v)) = 0) (hinf : ∀ v : InfinitePlace ℚ, x (Sum.inr v) = 0) :
    Additive.toMul (PhiF S F x) ∈ unitIdelesTrivialOn (𝓞 ↥F) ↥F (TT S F) := by
  change Additive.toMul (PhiF S F x) ∈ NumberField.AdeleRing.unitIdelesOutside _ _ _ ⊓ idelesTrivialOn _ _ _
  rw [Subgroup.mem_inf]
  refine ⟨?_, ?_⟩
  · have hr : PhiF S F x ∈ (NumberField.AdeleRing.unitIdelesOutside (𝓞 ↥F) ↥F {w | w.under (𝓞 ℚ) ∈ Sq S}).toAddSubgroup := by
      rw [← show (PhiF S F).range = _ from PhiF_range S F]; exact ⟨x, rfl⟩
    rw [TT_eq S F]
    exact hr
  · rw [mem_idelesTrivialOn_iff]
    refine ⟨?_, fun w hw => ?_⟩
    ·
      apply Units.ext
      funext w
      let v : InfinitePlace ℚ := w.comap (algebraMap ℚ ↥F)
      obtain ⟨y, hy⟩ : ∃ y : ↥F ≃ₐ[ℚ] ↥F, y • w = NumberField.ArchIdele.above ℚ ↥F v :=
        NumberField.InfinitePlace.exists_smul_eq_of_comap_eq (Subsingleton.elim _ _)
      have e' : NumberField.InfinitePlaceTransport.transport y hy
          (((Additive.toMul (PhiF S F x) : (AdeleRing (𝓞 ↥F) ↥F)ˣ) : AdeleRing (𝓞 ↥F) ↥F).1 w) = 1 :=
        (PhiF_inf S F x v w y hy).trans (by rw [hinf v]; rfl)
      rw [coe_infPart_apply]
      exact (NumberField.InfinitePlaceTransport.transport y hy).injective (e'.trans (map_one _).symm)
    ·
      have hv : w.under (𝓞 ℚ) ∈ Sq S := (under_mem_Sq_iff S ↥F w).2 hw
      let v : {v // v ∈ Sq S} := ⟨w.under (𝓞 ℚ), hv⟩
      have ho : NumberField.PlaceAbove.above ℚ ↥F v.1 ∈ MulAction.orbit (↥F ≃ₐ[ℚ] ↥F) w := by
        rw [NumberField.PlaceTransport.orbit_eq_setOf_under_eq ℚ ↥F w]
        exact NumberField.SUnits.under_above ℚ ↥F v.1
      obtain ⟨y, hy⟩ := MulAction.mem_orbit_iff.1 ho
      have e' : NumberField.PlaceTransport.transport y hy
          (((Additive.toMul (PhiF S F x) : (AdeleRing (𝓞 ↥F) ↥F)ˣ) : AdeleRing (𝓞 ↥F) ↥F).2 w) = 1 :=
        (PhiF_S S F x v w y hy).trans (by rw [hS v]; rfl)
      apply Units.ext
      rw [coe_finPart_apply, Units.val_one]
      exact (NumberField.PlaceTransport.transport y hy).injective (e'.trans (map_one _).symm)

theorem exists_LF_hom_eq_of_mem_unitIdelesOutside (z : (AdeleRing (𝓞 ↥F) ↥F)ˣ)
    (hz : z ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 ↥F) ↥F {w | w.under (𝓞 ℚ) ∈ Sq S}) :
    ∃ y : NumberField.SArchIdele.obj ℚ ↥F (Sq S),
      (LF S F).hom y = Additive.ofMul (QuotientGroup.mk z : SIdeleClassGroup (𝓞 ↥F) ↥F (TT S F)) := by
  have hz' : Additive.ofMul z ∈ (PhiF S F).range := by rw [show (PhiF S F).range = _ from PhiF_range S F]; exact hz
  obtain ⟨x, hx⟩ := hz'

  let y : NumberField.SArchIdele.obj ℚ ↥F (Sq S) := fun i => match i with
    | Sum.inl v => x (Sum.inl (Sum.inl v))
    | Sum.inr v => x (Sum.inr v)

  let x' : NumberField.SIdele.obj ℚ ↥F (Sq S) := x - (NumberField.SArchIdele.toSIdele ℚ ↥F (Sq S)).hom y
  have hS' : ∀ v : {v // v ∈ Sq S}, x' (Sum.inl (Sum.inl v)) = 0 := fun v => by
    change x (Sum.inl (Sum.inl v)) - (NumberField.SArchIdele.toSIdele ℚ ↥F (Sq S)).hom y (Sum.inl (Sum.inl v)) = 0
    rw [NumberField.SArchIdele.toSIdele_hom_apply_inl_inl]
    exact sub_self _
  have hinf' : ∀ v : InfinitePlace ℚ, x' (Sum.inr v) = 0 := fun v => by
    change x (Sum.inr v) - (NumberField.SArchIdele.toSIdele ℚ ↥F (Sq S)).hom y (Sum.inr v) = 0
    rw [NumberField.SArchIdele.toSIdele_hom_apply_inr]
    exact sub_self _
  have hmem := toMul_PhiF_mem_unitIdelesTrivialOn S F x' hS' hinf'
  have hxsplit : x = (NumberField.SArchIdele.toSIdele ℚ ↥F (Sq S)).hom y + x' := (add_sub_cancel _ _).symm
  refine ⟨y, ?_⟩

  unfold LF
  rw [LS_hom_apply, toSIdeleClass_mk]
  congr 1

  have hzz : z = Additive.toMul (PhiF S F ((NumberField.SArchIdele.toSIdele ℚ ↥F (Sq S)).hom y)) * Additive.toMul (PhiF S F x') := by
    rw [← toMul_add, ← map_add, ← hxsplit, hx]; rfl
  rw [hzz, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).2 (unitIdelesTrivialOn_le_sClassKernel _ _ _ hmem), mul_one]

scoped instance finite_repCokernel_LF : Finite (GroupCohomology.RepCokernel.obj (LF S F)) := by
  let P := principalIdeles (𝓞 ↥F) ↥F
  let U := NumberField.AdeleRing.unitIdelesOutside (𝓞 ↥F) ↥F {w | w.under (𝓞 ℚ) ∈ Sq S}
  haveI hPU : (P ⊔ U).FiniteIndex := NumberField.AdeleRing.finiteIndex_principalIdeles_sup_unitIdelesOutside ℚ ↥F (Sq S)
  let C := GroupCohomology.RepCokernel.obj (LF S F)
  let pr : CS S F ⟶ C := GroupCohomology.RepCokernel.π (LF S F)

  let ψ : (AdeleRing (𝓞 ↥F) ↥F)ˣ →* Multiplicative C :=
    { toFun := fun z => Multiplicative.ofAdd (pr.hom (Additive.ofMul (QuotientGroup.mk z : SIdeleClassGroup (𝓞 ↥F) ↥F (TT S F))))
      map_one' := by
        rw [QuotientGroup.mk_one]
        change Multiplicative.ofAdd (pr.hom 0) = 1
        rw [map_zero]; rfl
      map_mul' := fun a b => by
        rw [QuotientGroup.mk_mul]
        change Multiplicative.ofAdd (pr.hom (Additive.ofMul (QuotientGroup.mk a : SIdeleClassGroup (𝓞 ↥F) ↥F (TT S F)) +
          Additive.ofMul (QuotientGroup.mk b : SIdeleClassGroup (𝓞 ↥F) ↥F (TT S F)))) = _
        exact congrArg Multiplicative.ofAdd (pr.hom.toLinearMap.map_add _ _) }
  have hψ : ∀ z, ψ z = Multiplicative.ofAdd (pr.hom (Additive.ofMul (QuotientGroup.mk z : SIdeleClassGroup (𝓞 ↥F) ↥F (TT S F)))) :=
    fun _ => rfl
  have hker : P ⊔ U ≤ ψ.ker := by
    intro z hz
    rw [MonoidHom.mem_ker]
    obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.1 hz
    rw [map_mul]
    have h1 : ψ a = 1 := by
      rw [hψ, (QuotientGroup.eq_one_iff a).2 (principalIdeles_le_sClassKernel _ _ _ ha)]
      change Multiplicative.ofAdd (pr.hom 0) = 1
      rw [map_zero]; rfl
    have h2 : ψ b = 1 := by
      obtain ⟨y, hy⟩ := exists_LF_hom_eq_of_mem_unitIdelesOutside S F b hb
      have h0 : pr.hom ((LF S F).hom y) = 0 :=
        (GroupCohomology.RepCokernel.π_hom_apply_eq_zero_iff _ _).2 ⟨y, rfl⟩
      rw [hy] at h0
      rw [hψ]
      exact congrArg Multiplicative.ofAdd h0
    rw [h1, h2, one_mul]
  let ψ' := QuotientGroup.lift (P ⊔ U) ψ hker
  have hsurj : Function.Surjective ψ' := by
    intro c
    obtain ⟨d, hd⟩ := GroupCohomology.RepCokernel.π_hom_surjective (LF S F) (Multiplicative.toAdd c)
    obtain ⟨z, hz⟩ := QuotientGroup.mk_surjective (Additive.toMul d)
    refine ⟨QuotientGroup.mk z, ?_⟩
    rw [QuotientGroup.lift_mk, hψ, hz]
    change Multiplicative.ofAdd (pr.hom d) = c
    rw [hd]; rfl
  haveI : Finite ((AdeleRing (𝓞 ↥F) ↥F)ˣ ⧸ (P ⊔ U)) := Subgroup.finite_quotient_of_finiteIndex
  exact Finite.of_surjective (fun q => Multiplicative.toAdd (ψ' q)) fun c => by
    obtain ⟨q, hq⟩ := hsurj (Multiplicative.ofAdd c)
    exact ⟨q, by change Multiplicative.toAdd (ψ' q) = c; rw [hq]; rfl⟩

end fincoker
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95 P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95.Infl"

end Reduce95
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95 P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95.Infl"

set_option autoImplicit false
open CategoryTheory

namespace Reduce95
namespace RepCokernel

universe u

variable {k G G' : Type u} [CommRing k] [Group G] [Group G'] (π : G' →* G)
  {X Y : Rep.{u} k G} (f : X ⟶ Y) {X' Y' : Rep.{u} k G'} (f' : X' ⟶ Y') (β : Rep.res π Y ⟶ Y')

theorem range_le_comap_of_sq (α : Rep.res π X ⟶ X') (w : (Rep.resFunctor π).map f ≫ β = α ≫ f') :
    LinearMap.range f.hom.toLinearMap ≤ (LinearMap.range f'.hom.toLinearMap).comap β.hom.toLinearMap := by
  rintro _ ⟨x, rfl⟩
  refine ⟨α.hom x, ?_⟩
  have h := congrArg (fun φ : Rep.res π X ⟶ Y' => φ.hom x) w
  exact h.symm

noncomputable def mapRes (h : LinearMap.range f.hom.toLinearMap ≤ (LinearMap.range f'.hom.toLinearMap).comap β.hom.toLinearMap) :
    Rep.res π (GroupCohomology.RepCokernel.obj f) ⟶ GroupCohomology.RepCokernel.obj f' :=
  Rep.ofHom ⟨Submodule.mapQ _ _ β.hom.toLinearMap h, fun g => LinearMap.ext fun q => by
    induction q using Submodule.Quotient.induction_on with
    | _ y =>
      change Submodule.mapQ _ _ β.hom.toLinearMap h (Submodule.Quotient.mk (Y.ρ (π g) y)) =
        (GroupCohomology.RepCokernel.obj f').ρ g (Submodule.mapQ _ _ β.hom.toLinearMap h (Submodule.Quotient.mk y))
      rw [Submodule.mapQ_apply, Submodule.mapQ_apply]
      change Submodule.Quotient.mk (β.hom ((Rep.res π Y).ρ g y)) = Submodule.Quotient.mk (Y'.ρ g (β.hom y))
      rw [Rep.hom_comm_apply]⟩

theorem mapRes_hom_mk (h : LinearMap.range f.hom.toLinearMap ≤ (LinearMap.range f'.hom.toLinearMap).comap β.hom.toLinearMap) (y : Y) :
    (mapRes π f f' β h).hom (Submodule.Quotient.mk y : GroupCohomology.RepCokernel.obj f) =
      (Submodule.Quotient.mk (β.hom y) : GroupCohomology.RepCokernel.obj f') := rfl

theorem mapRes_hom_π (h : LinearMap.range f.hom.toLinearMap ≤ (LinearMap.range f'.hom.toLinearMap).comap β.hom.toLinearMap) (y : Y) :
    (mapRes π f f' β h).hom ((GroupCohomology.RepCokernel.π f).hom y) = (GroupCohomology.RepCokernel.π f').hom (β.hom y) := rfl

theorem res_π_comp_mapRes (h : LinearMap.range f.hom.toLinearMap ≤ (LinearMap.range f'.hom.toLinearMap).comap β.hom.toLinearMap) :
    (Rep.resFunctor π).map (GroupCohomology.RepCokernel.π f) ≫ mapRes π f f' β h = β ≫ GroupCohomology.RepCokernel.π f' :=
  Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun _ => rfl))

noncomputable abbrev mapResOfSq (α : Rep.res π X ⟶ X') (w : (Rep.resFunctor π).map f ≫ β = α ≫ f') :
    Rep.res π (GroupCohomology.RepCokernel.obj f) ⟶ GroupCohomology.RepCokernel.obj f' :=
  mapRes π f f' β (range_le_comap_of_sq π f f' β α w)

theorem res_π_comp_mapResOfSq (α : Rep.res π X ⟶ X') (w : (Rep.resFunctor π).map f ≫ β = α ≫ f') :
    (Rep.resFunctor π).map (GroupCohomology.RepCokernel.π f) ≫ mapResOfSq π f f' β α w = β ≫ GroupCohomology.RepCokernel.π f' :=
  res_π_comp_mapRes π f f' β _

theorem mapRes_hom_mk_eq_zero_iff (h : LinearMap.range f.hom.toLinearMap ≤ (LinearMap.range f'.hom.toLinearMap).comap β.hom.toLinearMap)
    (y : Y) :
    (mapRes π f f' β h).hom (Submodule.Quotient.mk y : GroupCohomology.RepCokernel.obj f) = 0 ↔
      β.hom y ∈ LinearMap.range f'.hom.toLinearMap := by
  rw [mapRes_hom_mk]
  exact Submodule.Quotient.mk_eq_zero _

end Reduce95.RepCokernel
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95 P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95.Infl"
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95 P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95.Infl"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxSynthPendingDepth 3
open CategoryTheory IsDedekindDomain NumberField

namespace Reduce95
open ExtCitation groupCohomology GroupCohomology M4aHerbrand
open scoped NumberField.PlaceDecomp

section pitInputs

variable (S : Finset Nat.Primes) (F F₁ : IntermediateField ℚ (AlgebraicClosure ℚ))
  [NumberField ↥F] [IsGalois ℚ ↥F] [NumberField ↥F₁] [IsGalois ℚ ↥F₁] [hle : Fact (F ≤ F₁)]
  (J : AdeleRing (𝓞 ↥F) ↥F →+* AdeleRing (𝓞 ↥F₁) ↥F₁)
  (hJF : ∀ a : ↥F, J (algebraMap ↥F (AdeleRing (𝓞 ↥F) ↥F) a) = algebraMap ↥F₁ (AdeleRing (𝓞 ↥F₁) ↥F₁) (algebraMap ↥F ↥F₁ a))
  (hJeq : ∀ (g' : ↥F₁ ≃ₐ[ℚ] ↥F₁) (x : AdeleRing (𝓞 ↥F) ↥F), J ((DD F).act (AlgEquiv.restrictNormalHom ↥F g') x) = (DD F₁).act g' (J x))
  (hJout : ∀ (T : Set (HeightOneSpectrum (𝓞 ℚ))) (z : (AdeleRing (𝓞 ↥F) ↥F)ˣ),
    (∀ w : HeightOneSpectrum (𝓞 ↥F), w.under (𝓞 ℚ) ∉ T → finPart w z = 1) →
    ∀ w' : HeightOneSpectrum (𝓞 ↥F₁), w'.under (𝓞 ℚ) ∉ T →
      finPart w' (Units.map (J : AdeleRing (𝓞 ↥F) ↥F →* AdeleRing (𝓞 ↥F₁) ↥F₁) z) = 1)
  (hJunit : ∀ (T : Set (HeightOneSpectrum (𝓞 ℚ))) (z : (AdeleRing (𝓞 ↥F) ↥F)ˣ),
    z ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 ↥F) ↥F {w | w.under (𝓞 ℚ) ∈ T} →
    Units.map (J : AdeleRing (𝓞 ↥F) ↥F →* AdeleRing (𝓞 ↥F₁) ↥F₁) z ∈
      NumberField.AdeleRing.unitIdelesOutside (𝓞 ↥F₁) ↥F₁ {w' | w'.under (𝓞 ℚ) ∈ T})
  (hJinf : ∀ z : (AdeleRing (𝓞 ↥F) ↥F)ˣ, infPart z = 1 → infPart (Units.map (J : AdeleRing (𝓞 ↥F) ↥F →* AdeleRing (𝓞 ↥F₁) ↥F₁) z) = 1)

theorem hTcl : (GroupCohomology.RepImage.seq (LF S F)).ShortExact := GroupCohomology.RepImage.seq_shortExact (LF S F)

noncomputable abbrev jCl : Rep.res (levelMapR F F₁ hle.out) (GroupCohomology.RepCokernel.obj (LF S F)) ⟶
    GroupCohomology.RepCokernel.obj (LF S F₁) :=
  RepCokernel.mapResOfSq (levelMapR F F₁ hle.out) (LF S F) (LF S F₁)
    (jC S F F₁ J hJF hJeq hJout hJunit hJinf) (jJ S F F₁ J hJeq hJout) (hsqC S F F₁ J hJF hJeq hJout hJunit hJinf)

theorem hsqCl : (Rep.resFunctor (levelMapR F F₁ hle.out)).map (GroupCohomology.RepImage.seq (LF S F)).g ≫ jCl S F F₁ J hJF hJeq hJout hJunit hJinf =
    jC S F F₁ J hJF hJeq hJout hJunit hJinf ≫ (GroupCohomology.RepImage.seq (LF S F₁)).g :=
  RepCokernel.res_π_comp_mapResOfSq _ _ _ _ _ _

theorem exists_pow_mem_of_smul_mk_eq_zero (p : ℕ) (z : (AdeleRing (𝓞 ↥F) ↥F)ˣ) (k : ℕ)
    (h : p ^ k • (Submodule.Quotient.mk (Additive.ofMul (QuotientGroup.mk z : SIdeleClassGroup (𝓞 ↥F) ↥F (TT S F))) :
      GroupCohomology.RepCokernel.obj (LF S F)) = 0) :
    z ^ p ^ k ∈ principalIdeles (𝓞 ↥F) ↥F ⊔ NumberField.AdeleRing.unitIdelesOutside (𝓞 ↥F) ↥F {w | w.under (𝓞 ℚ) ∈ Sq S} := by
  have h2 : (Submodule.Quotient.mk (p ^ k • Additive.ofMul (QuotientGroup.mk z : SIdeleClassGroup (𝓞 ↥F) ↥F (TT S F))) :
      GroupCohomology.RepCokernel.obj (LF S F)) = 0 := by
    rw [← h]
    exact map_nsmul (Submodule.mkQ _) (p ^ k) _
  rw [Submodule.Quotient.mk_eq_zero] at h2
  obtain ⟨y, hy⟩ := h2

  have hy' : (QuotientGroup.mk (Additive.toMul (PhiF S F ((NumberField.SArchIdele.toSIdele ℚ ↥F (Sq S)).hom y))) :
      SIdeleClassGroup (𝓞 ↥F) ↥F (TT S F)) = QuotientGroup.mk (z ^ p ^ k) := by
    have h1 : (LF S F).hom y = Additive.ofMul (QuotientGroup.mk (Additive.toMul (PhiF S F ((NumberField.SArchIdele.toSIdele ℚ ↥F (Sq S)).hom y))) :
        SIdeleClassGroup (𝓞 ↥F) ↥F (TT S F)) := by
      unfold LF; rw [LS_hom_apply, toSIdeleClass_mk]
    have hy2 := congrArg Additive.toMul (h1.symm.trans hy)
    rw [toMul_ofMul, ← ofMul_pow, toMul_ofMul, ← QuotientGroup.mk_pow] at hy2
    exact hy2

  obtain ⟨s, hs, hzs⟩ : ∃ s ∈ sClassKernel (𝓞 ↥F) ↥F (TT S F),
      Additive.toMul (PhiF S F ((NumberField.SArchIdele.toSIdele ℚ ↥F (Sq S)).hom y)) * s = z ^ p ^ k := by
    refine ⟨(Additive.toMul (PhiF S F ((NumberField.SArchIdele.toSIdele ℚ ↥F (Sq S)).hom y)))⁻¹ * z ^ p ^ k, ?_, mul_inv_cancel_left _ _⟩
    rw [← QuotientGroup.eq]
    exact hy'
  rw [← hzs]
  have hΦ : Additive.toMul (PhiF S F ((NumberField.SArchIdele.toSIdele ℚ ↥F (Sq S)).hom y)) ∈
      NumberField.AdeleRing.unitIdelesOutside (𝓞 ↥F) ↥F {w | w.under (𝓞 ℚ) ∈ Sq S} := by
    have hr : PhiF S F ((NumberField.SArchIdele.toSIdele ℚ ↥F (Sq S)).hom y) ∈
        (NumberField.AdeleRing.unitIdelesOutside (𝓞 ↥F) ↥F {w | w.under (𝓞 ℚ) ∈ Sq S}).toAddSubgroup := by
      rw [← show (PhiF S F).range = _ from PhiF_range S F]; exact ⟨_, rfl⟩
    exact hr
  refine Subgroup.mul_mem _ (Subgroup.mem_sup_right hΦ) ?_

  refine (sup_le_sup_left ((unitIdelesTrivialOn_le_unitIdelesOutside (𝓞 ↥F) ↥F (TT S F)).trans (le_of_eq ?_)) _) hs
  rw [TT_eq S F]
  rfl

include hJF hJeq hJout hJunit hJinf in

theorem hpit_of_cap (p : ℕ)
    (hcap : ∀ z : (AdeleRing (𝓞 ↥F) ↥F)ˣ,
      (∃ k : ℕ, z ^ p ^ k ∈ principalIdeles (𝓞 ↥F) ↥F ⊔ NumberField.AdeleRing.unitIdelesOutside (𝓞 ↥F) ↥F {w | w.under (𝓞 ℚ) ∈ Sq S}) →
      JJ F F₁ J z ∈ principalIdeles (𝓞 ↥F₁) ↥F₁ ⊔ NumberField.AdeleRing.unitIdelesOutside (𝓞 ↥F₁) ↥F₁ {w | w.under (𝓞 ℚ) ∈ Sq S})
    (c : GroupCohomology.RepCokernel.obj (LF S F)) (hc : ∃ k : ℕ, p ^ k • c = 0) :
    (jCl S F F₁ J hJF hJeq hJout hJunit hJinf).hom c = 0 := by
  induction c using Submodule.Quotient.induction_on with
  | _ d =>
    obtain ⟨zc, hzc⟩ := QuotientGroup.mk_surjective (Additive.toMul d)
    have hd : d = Additive.ofMul (QuotientGroup.mk zc : SIdeleClassGroup (𝓞 ↥F) ↥F (TT S F)) := by
      rw [hzc]; rfl
    subst hd
    obtain ⟨k, hk⟩ := hc
    have hz := hcap zc ⟨k, exists_pow_mem_of_smul_mk_eq_zero S F p zc k hk⟩
    obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup.1 hz
    rw [RepCokernel.mapRes_hom_mk_eq_zero_iff]

    obtain ⟨y₁, hy₁⟩ := exists_LF_hom_eq_of_mem_unitIdelesOutside S F₁ b hb
    refine ⟨y₁, ?_⟩
    change (LF S F₁).hom y₁ = (jC S F F₁ J hJF hJeq hJout hJunit hJinf).hom (Additive.ofMul (QuotientGroup.mk zc : SIdeleClassGroup (𝓞 ↥F) ↥F (TT S F)))
    rw [hy₁, jC_hom_apply]
    change Additive.ofMul (QuotientGroup.mk b : SIdeleClassGroup (𝓞 ↥F₁) ↥F₁ (TT S F₁)) =
      Additive.ofMul (sClassMapJ S F F₁ J hJF hJout hJunit hJinf (QuotientGroup.mk zc))
    rw [sClassMapJ_mk, ← hab, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff a).2 (principalIdeles_le_sClassKernel _ _ _ ha), one_mul]

variable {p : ℕ} [Fact p.Prime] (B : Rep ℤ (↥F ≃ₐ[ℚ] ↥F)) (hB : ∀ b : B, p • b = 0)
  (hcap : ∀ z : (AdeleRing (𝓞 ↥F) ↥F)ˣ,
    (∃ k : ℕ, z ^ p ^ k ∈ principalIdeles (𝓞 ↥F) ↥F ⊔ NumberField.AdeleRing.unitIdelesOutside (𝓞 ↥F) ↥F {w | w.under (𝓞 ℚ) ∈ Sq S}) →
    JJ F F₁ J z ∈ principalIdeles (𝓞 ↥F₁) ↥F₁ ⊔ NumberField.AdeleRing.unitIdelesOutside (𝓞 ↥F₁) ↥F₁ {w | w.under (𝓞 ℚ) ∈ Sq S})

set_option maxHeartbeats 3200000 in
include hB hcap in

theorem hPITker_inst (t : Rep.relationModuleInt B ⟶ (seqF S F).X₃) (χ : Rep.free ℤ (↥F ≃ₐ[ℚ] ↥F) B ⟶ CS S F)
    (h : t ≫ GroupCohomology.RepImage.ι (LF S F) = Rep.relationModuleInt.ι B ≫ χ) :
    ∃ χ' : Rep.free ℤ (↥F₁ ≃ₐ[ℚ] ↥F₁) (Rep.res (levelMapR F F₁ hle.out) B) ⟶ (seqF S F₁).X₃,
      Infl.inflHom (levelMapR F F₁ hle.out) B (jY S F F₁ J hJF hJeq hJout hJunit hJinf) t =
        Rep.relationModuleInt.ι (Rep.res (levelMapR F F₁ hle.out) B) ≫ χ' := by
  haveI : Fintype (↥F ≃ₐ[ℚ] ↥F) := Fintype.ofFinite _
  haveI : Fintype (↥F₁ ≃ₐ[ℚ] ↥F₁) := Fintype.ofFinite _
  haveI : Finite (GroupCohomology.RepImage.seq (LF S F)).X₃ := finite_repCokernel_LF S F
  haveI : Finite (GroupCohomology.RepImage.seq (LF S F₁)).X₃ := finite_repCokernel_LF S F₁
  exact hPITker_gen (levelMapR F F₁ hle.out) B p hB (hTcl S F) (hTcl S F₁)
    (jY S F F₁ J hJF hJeq hJout hJunit hJinf) (jC S F F₁ J hJF hJeq hJout hJunit hJinf) (jCl S F F₁ J hJF hJeq hJout hJunit hJinf)
    (hsqCι S F F₁ J hJF hJeq hJout hJunit hJinf) (hsqCl S F F₁ J hJF hJeq hJout hJunit hJinf)
    (hpit_of_cap S F F₁ J hJF hJeq hJout hJunit hJinf p hcap)
    (Infl.inflHom (levelMapR F F₁ hle.out) B (jY S F F₁ J hJF hJeq hJout hJunit hJinf))
    (fun t => Infl.inflHom_apply (levelMapR F F₁ hle.out) B (jY S F F₁ J hJF hJeq hJout hJunit hJinf) t) t χ h

set_option maxHeartbeats 3200000 in
include hB hcap in

theorem hPITco_inst (φ : Rep.relationModuleInt B ⟶ CS S F) :
    ∃ (t : Rep.relationModuleInt (Rep.res (levelMapR F F₁ hle.out) B) ⟶ (seqF S F₁).X₃)
      (χ : Rep.free ℤ (↥F₁ ≃ₐ[ℚ] ↥F₁) (Rep.res (levelMapR F F₁ hle.out) B) ⟶ CS S F₁),
      Infl.inflHom (levelMapR F F₁ hle.out) B (jC S F F₁ J hJF hJeq hJout hJunit hJinf) φ =
        t ≫ GroupCohomology.RepImage.ι (LF S F₁) + Rep.relationModuleInt.ι (Rep.res (levelMapR F F₁ hle.out) B) ≫ χ := by
  haveI : Fintype (↥F ≃ₐ[ℚ] ↥F) := Fintype.ofFinite _
  haveI : Fintype (↥F₁ ≃ₐ[ℚ] ↥F₁) := Fintype.ofFinite _
  haveI : Finite (GroupCohomology.RepImage.seq (LF S F)).X₃ := finite_repCokernel_LF S F
  haveI : Finite (GroupCohomology.RepImage.seq (LF S F₁)).X₃ := finite_repCokernel_LF S F₁
  exact hPITco_gen (levelMapR F F₁ hle.out) B p hB (hTcl S F) (hTcl S F₁)
    (jY S F F₁ J hJF hJeq hJout hJunit hJinf) (jC S F F₁ J hJF hJeq hJout hJunit hJinf) (jCl S F F₁ J hJF hJeq hJout hJunit hJinf)
    (hsqCι S F F₁ J hJF hJeq hJout hJunit hJinf) (hsqCl S F F₁ J hJF hJeq hJout hJunit hJinf)
    (hpit_of_cap S F F₁ J hJF hJeq hJout hJunit hJinf p hcap)
    (Infl.inflHom (levelMapR F F₁ hle.out) B (jC S F F₁ J hJF hJeq hJout hJunit hJinf))
    (fun φ => Infl.inflHom_apply (levelMapR F F₁ hle.out) B (jC S F F₁ J hJF hJeq hJout hJunit hJinf) φ) φ

end pitInputs
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95 P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95.Infl"

end Reduce95
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95 P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95.Infl"

set_option autoImplicit false
open CategoryTheory IsDedekindDomain NumberField

namespace Reduce95
open ExtCitation groupCohomology M4aHerbrand
open scoped NumberField.PlaceDecomp NumberField.PlaceTransport

section towerEpin

variable (S : Finset Nat.Primes) (F F₁ : IntermediateField ℚ (AlgebraicClosure ℚ))
  [NumberField ↥F] [IsGalois ℚ ↥F] [NumberField ↥F₁] [IsGalois ℚ ↥F₁] [hle : Fact (F ≤ F₁)]
  (J : AdeleRing (𝓞 ↥F) ↥F →+* AdeleRing (𝓞 ↥F₁) ↥F₁)
  (hJF : ∀ a : ↥F, J (algebraMap ↥F (AdeleRing (𝓞 ↥F) ↥F) a) = algebraMap ↥F₁ (AdeleRing (𝓞 ↥F₁) ↥F₁) (algebraMap ↥F ↥F₁ a))
  (hJeq : ∀ (g' : ↥F₁ ≃ₐ[ℚ] ↥F₁) (x : AdeleRing (𝓞 ↥F) ↥F), J ((DD F).act (AlgEquiv.restrictNormalHom ↥F g') x) = (DD F₁).act g' (J x))
  (hJout : ∀ (T : Set (HeightOneSpectrum (𝓞 ℚ))) (z : (AdeleRing (𝓞 ↥F) ↥F)ˣ),
    (∀ w : HeightOneSpectrum (𝓞 ↥F), w.under (𝓞 ℚ) ∉ T → finPart w z = 1) →
    ∀ w' : HeightOneSpectrum (𝓞 ↥F₁), w'.under (𝓞 ℚ) ∉ T →
      finPart w' (Units.map (J : AdeleRing (𝓞 ↥F) ↥F →* AdeleRing (𝓞 ↥F₁) ↥F₁) z) = 1)
  (hJunit : ∀ (T : Set (HeightOneSpectrum (𝓞 ℚ))) (z : (AdeleRing (𝓞 ↥F) ↥F)ˣ),
    z ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 ↥F) ↥F {w | w.under (𝓞 ℚ) ∈ T} →
    Units.map (J : AdeleRing (𝓞 ↥F) ↥F →* AdeleRing (𝓞 ↥F₁) ↥F₁) z ∈
      NumberField.AdeleRing.unitIdelesOutside (𝓞 ↥F₁) ↥F₁ {w' | w'.under (𝓞 ℚ) ∈ T})
  (hJinf : ∀ z : (AdeleRing (𝓞 ↥F) ↥F)ˣ, infPart z = 1 → infPart (Units.map (J : AdeleRing (𝓞 ↥F) ↥F →* AdeleRing (𝓞 ↥F₁) ↥F₁) z) = 1)

  (q₀ : ↥S)

  (hJloc : ∀ (z z' : (AdeleRing (𝓞 ↥F) ↥F)ˣ) (w' : HeightOneSpectrum (𝓞 ↥F₁)),
    finPart (w'.under (𝓞 ↥F)) z = finPart (w'.under (𝓞 ↥F)) z' → finPart w' (JJ F F₁ J z) = finPart w' (JJ F F₁ J z'))

local notation "πT" => levelMapR F F₁ (Fact.out : F ≤ F₁)
local notation "E_" K => NumberField.SUnits.sUnitsRep ℚ (↥K) (Sq S)
local notation "dg" K => NumberField.SArchIdele.diagS ℚ (↥K) (Sq S)

omit [IsGalois ℚ ↥F] in

theorem coe_finPart_unitsMap_algebraMap (w : HeightOneSpectrum (𝓞 ↥F)) (u : (↥F)ˣ) :
    (finPart w (Units.map (algebraMap ↥F (AdeleRing (𝓞 ↥F) ↥F) : ↥F →* AdeleRing (𝓞 ↥F) ↥F) u) : w.adicCompletion ↥F) =
      algebraMap ↥F (w.adicCompletion ↥F) (u : ↥F) := by
  rw [coe_finPart_apply, Units.coe_map, MonoidHom.coe_coe]
  rfl

theorem finPart_PhiF_diag_eq_finPart_PhiF_toSIdele_diagS (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥K] [IsGalois ℚ ↥K]
    (x : E_ K) (w : HeightOneSpectrum (𝓞 ↥K)) (hw : w.under (𝓞 ℚ) ∈ Sq S) :
    finPart w (Additive.toMul (PhiF S K ((NumberField.SIdele.diag ℚ ↥K (Sq S)).hom x))) =
      finPart w (Additive.toMul (PhiF S K ((NumberField.SArchIdele.toSIdele ℚ ↥K (Sq S)).hom ((dg K).hom x)))) := by
  obtain ⟨y, hy⟩ := exists_smul_eq_above ↥K w
  have h1 := PhiF_S S K ((NumberField.SIdele.diag ℚ ↥K (Sq S)).hom x) ⟨_, hw⟩ w y hy
  have h2 := PhiF_S S K ((NumberField.SArchIdele.toSIdele ℚ ↥K (Sq S)).hom ((dg K).hom x)) ⟨_, hw⟩ w y hy
  rw [NumberField.SArchIdele.toSIdele_diagS_apply_inl_inl] at h2
  apply Units.ext
  rw [coe_finPart_apply, coe_finPart_apply]
  exact (NumberField.PlaceTransport.transport y hy).injective (h1.trans h2.symm)

omit [NumberField ↥F] [IsGalois ℚ ↥F] [NumberField ↥F₁] [IsGalois ℚ ↥F₁] in

theorem under_under_rat (w' : HeightOneSpectrum (𝓞 ↥F₁)) : (w'.under (𝓞 ↥F)).under (𝓞 ℚ) = w'.under (𝓞 ℚ) :=
  HeightOneSpectrum.ext (Ideal.under_under (A := 𝓞 ℚ) (B := 𝓞 ↥F) (𝔓 := w'.asIdeal))

include hJF hJloc q₀ in

theorem hjE (x : E_ F) :
    iotaE F₁ (Sq S) ((jE S F F₁ J hJF hJeq hJout hJunit hJinf).hom x) = iotaE F (Sq S) x := by

  set w₁ : HeightOneSpectrum (𝓞 ↥F₁) := NumberField.PlaceAbove.above ℚ ↥F₁ (placeOf q₀.1) with hw₁
  have hw₁S : w₁.under (𝓞 ℚ) ∈ Sq S := by
    rw [hw₁, NumberField.SUnits.under_above]; exact (eS S q₀).2
  have hwS : (w₁.under (𝓞 ↥F)).under (𝓞 ℚ) ∈ Sq S := by rw [under_under_rat]; exact hw₁S
  set e₁ := (jE S F F₁ J hJF hJeq hJout hJunit hJinf).hom x with he₁

  have h3 : finPart w₁ (Units.map (algebraMap ↥F₁ (AdeleRing (𝓞 ↥F₁) ↥F₁) : ↥F₁ →* _) (NumberField.SUnits.val ℚ ↥F₁ (Sq S) e₁)) =
      finPart w₁ (JJ F F₁ J (Additive.toMul (PhiF S F ((NumberField.SArchIdele.toSIdele ℚ ↥F (Sq S)).hom ((dg F).hom x))))) := by
    have hd : Additive.toMul (PhiF S F₁ ((NumberField.SIdele.diag ℚ ↥F₁ (Sq S)).hom e₁)) =
        Units.map (algebraMap ↥F₁ (AdeleRing (𝓞 ↥F₁) ↥F₁) : ↥F₁ →* _) (NumberField.SUnits.val ℚ ↥F₁ (Sq S) e₁) :=
      (congrArg Additive.toMul (PhiF_diag S F₁ e₁)).trans (toMul_ofMul _)
    rw [← hd, finPart_PhiF_diag_eq_finPart_PhiF_toSIdele_diagS S F₁ e₁ w₁ hw₁S, he₁, jE_hom_apply,
      diagS_jEfun, jJ_spec, toMul_ofMul]

  have h12 : finPart w₁ (JJ F F₁ J (Additive.toMul (PhiF S F ((NumberField.SArchIdele.toSIdele ℚ ↥F (Sq S)).hom ((dg F).hom x))))) =
      finPart w₁ (JJ F F₁ J (Units.map (algebraMap ↥F (AdeleRing (𝓞 ↥F) ↥F) : ↥F →* _) (NumberField.SUnits.val ℚ ↥F (Sq S) x))) := by
    apply hJloc
    have hdx : Additive.toMul (PhiF S F ((NumberField.SIdele.diag ℚ ↥F (Sq S)).hom x)) =
        Units.map (algebraMap ↥F (AdeleRing (𝓞 ↥F) ↥F) : ↥F →* _) (NumberField.SUnits.val ℚ ↥F (Sq S) x) :=
      (congrArg Additive.toMul (PhiF_diag S F x)).trans (toMul_ofMul _)
    rw [← finPart_PhiF_diag_eq_finPart_PhiF_toSIdele_diagS S F x _ hwS, hdx]

  have hJJ : JJ F F₁ J (Units.map (algebraMap ↥F (AdeleRing (𝓞 ↥F) ↥F) : ↥F →* _) (NumberField.SUnits.val ℚ ↥F (Sq S) x)) =
      Units.map (algebraMap ↥F₁ (AdeleRing (𝓞 ↥F₁) ↥F₁) : ↥F₁ →* _)
        (Units.map (algebraMap ↥F ↥F₁ : ↥F →* ↥F₁) (NumberField.SUnits.val ℚ ↥F (Sq S) x)) :=
    Units.ext (hJF _)

  have hval : (NumberField.SUnits.val ℚ ↥F₁ (Sq S) e₁ : ↥F₁) = algebraMap ↥F ↥F₁ (NumberField.SUnits.val ℚ ↥F (Sq S) x : ↥F) := by
    have h := congrArg (fun u : (w₁.adicCompletion ↥F₁)ˣ => (u : w₁.adicCompletion ↥F₁)) (h3.trans (h12.trans (congrArg (finPart w₁) hJJ)))
    simp only [coe_finPart_unitsMap_algebraMap] at h
    exact (algebraMap ↥F₁ (w₁.adicCompletion ↥F₁)).injective h

  apply Additive.toMul.injective
  rw [toMul_iotaE, toMul_iotaE]
  apply Units.ext
  simp only [Units.coe_map, MonoidHom.coe_coe]
  rw [hval]
  exact inclAlg_algebraMap F F₁ hle.out _

end towerEpin
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95 P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95.Infl"

end Reduce95
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95 P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95.Infl"

set_option autoImplicit false
open CategoryTheory IsDedekindDomain NumberField

namespace Reduce95
open ExtCitation

section hmu

variable (S : Finset Nat.Primes) {p : ℕ} [Fact p.Prime]
  (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F]
  (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p) (hζF : ζ ∈ F)

omit [IsGalois ℚ ↥F] in

theorem valuation_eq_one_of_pow_eq_one {x : ↥F} {n : ℕ} (hn : n ≠ 0) (hx : x ^ n = 1)
    (σ : ↥F ≃ₐ[ℚ] ↥F) (w : HeightOneSpectrum (𝓞 ↥F)) : w.valuation ↥F (σ x) = 1 := by

  have hσx : (σ x) ^ n = 1 := by rw [← map_pow, hx, map_one]
  have hint : IsIntegral ℤ (σ x) := by
    refine IsIntegral.of_pow (Nat.pos_of_ne_zero hn) ?_
    rw [hσx]; exact isIntegral_one
  obtain ⟨r, hr⟩ : ∃ r : 𝓞 ↥F, (r : ↥F) = σ x := ⟨⟨σ x, hint⟩, rfl⟩
  have hle : w.valuation ↥F (σ x) ≤ 1 := by rw [← hr]; exact HeightOneSpectrum.valuation_le_one w r
  have hle' : w.valuation ↥F ((σ x) ^ (n - 1)) ≤ 1 := by
    rw [← hr, ← map_pow]; exact HeightOneSpectrum.valuation_le_one w (r ^ (n - 1))
  apply le_antisymm hle
  calc (1 : WithZero (Multiplicative ℤ)) = w.valuation ↥F ((σ x) ^ n) := by rw [hσx, map_one]
    _ = w.valuation ↥F (σ x) * w.valuation ↥F ((σ x) ^ (n - 1)) := by
        rw [← map_mul, ← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hn)]
    _ ≤ w.valuation ↥F (σ x) * 1 := mul_le_mul_right hle' _
    _ = w.valuation ↥F (σ x) := mul_one _

theorem zetaF_mem_sUnits : zetaF ζ hζ F hζF ∈ NumberField.SUnits.sUnits ℚ ↥F (Sq S) := by
  rw [NumberField.SUnits.mem_sUnits_iff]
  intro σ w _
  exact valuation_eq_one_of_pow_eq_one F (p_ne_zero' (p := p))
    (by rw [← Units.val_pow_eq_pow_val, zetaF_pow_p ζ hζ F hζF, Units.val_one]) σ w

noncomputable def zetaE : NumberField.SUnits.sUnitsRep ℚ ↥F (Sq S) :=
  ⟨Additive.ofMul (zetaF ζ hζ F hζF), (NumberField.SUnits.mem_sUnitsSubmodule ℚ ↥F (Sq S) _).2 (zetaF_mem_sUnits S F ζ hζ hζF)⟩

theorem val_zetaE : NumberField.SUnits.val ℚ ↥F (Sq S) (zetaE S F ζ hζ hζF) = zetaF ζ hζ F hζF := rfl

theorem iotaE_zetaE : iotaE F (Sq S) (zetaE S F ζ hζ hζF) = Additive.ofMul (zetaU ζ hζ) := by
  apply Additive.toMul.injective
  rw [toMul_iotaE, toMul_ofMul, val_zetaE, map_zetaF]

include hζ hζF in

theorem exists_sUnits_of_pow_eq_one (u : (AlgebraicClosure ℚ)ˣ) (hu : u ^ p = 1) :
    ∃ e : NumberField.SUnits.sUnitsRep ℚ ↥F (Sq S), iotaE F (Sq S) e = Additive.ofMul u := by
  obtain ⟨i, -, hi⟩ := (zetaU_prim ζ hζ).eq_pow_of_mem_rootsOfUnity ((mem_rootsOfUnity p u).mpr hu)
  refine ⟨i • zetaE S F ζ hζ hζF, ?_⟩
  rw [map_nsmul, iotaE_zetaE, ← ofMul_pow, hi]

end hmu
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95 P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95.Infl"
end Reduce95
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95 P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95.Infl"

set_option autoImplicit false
open CategoryTheory IsDedekindDomain NumberField

namespace Reduce95
open ExtCitation M4aHerbrand

section capPsi

variable (S : Finset Nat.Primes) (F F₁ : IntermediateField ℚ (AlgebraicClosure ℚ))
  [NumberField ↥F] [IsGalois ℚ ↥F] [NumberField ↥F₁] [IsGalois ℚ ↥F₁] [hle : Fact (F ≤ F₁)]
  (J : AdeleRing (𝓞 ↥F) ↥F →+* AdeleRing (𝓞 ↥F₁) ↥F₁)
  (hJF : ∀ a : ↥F, J (algebraMap ↥F (AdeleRing (𝓞 ↥F) ↥F) a) = algebraMap ↥F₁ (AdeleRing (𝓞 ↥F₁) ↥F₁) (algebraMap ↥F ↥F₁ a))
  (hJeq : ∀ (g' : ↥F₁ ≃ₐ[ℚ] ↥F₁) (x : AdeleRing (𝓞 ↥F) ↥F), J ((DD F).act (AlgEquiv.restrictNormalHom ↥F g') x) = (DD F₁).act g' (J x))
  (hJout : ∀ (T : Set (HeightOneSpectrum (𝓞 ℚ))) (z : (AdeleRing (𝓞 ↥F) ↥F)ˣ),
    (∀ w : HeightOneSpectrum (𝓞 ↥F), w.under (𝓞 ℚ) ∉ T → finPart w z = 1) →
    ∀ w' : HeightOneSpectrum (𝓞 ↥F₁), w'.under (𝓞 ℚ) ∉ T →
      finPart w' (Units.map (J : AdeleRing (𝓞 ↥F) ↥F →* AdeleRing (𝓞 ↥F₁) ↥F₁) z) = 1)
  (hJunit : ∀ (T : Set (HeightOneSpectrum (𝓞 ℚ))) (z : (AdeleRing (𝓞 ↥F) ↥F)ˣ),
    z ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 ↥F) ↥F {w | w.under (𝓞 ℚ) ∈ T} →
    Units.map (J : AdeleRing (𝓞 ↥F) ↥F →* AdeleRing (𝓞 ↥F₁) ↥F₁) z ∈
      NumberField.AdeleRing.unitIdelesOutside (𝓞 ↥F₁) ↥F₁ {w' | w'.under (𝓞 ℚ) ∈ T})
  (hJinf : ∀ z : (AdeleRing (𝓞 ↥F) ↥F)ˣ, infPart z = 1 → infPart (Units.map (J : AdeleRing (𝓞 ↥F) ↥F →* AdeleRing (𝓞 ↥F₁) ↥F₁) z) = 1)

  (Ψ : FiniteAdeleRing (𝓞 ↥F) ↥F →+* FiniteAdeleRing (𝓞 ↥F₁) ↥F₁)
  (hJΨ : ∀ z : AdeleRing (𝓞 ↥F) ↥F, (J z).2 = Ψ z.2)
  {p : ℕ}

  (hcapΨ : ∀ x : (FiniteAdeleRing (𝓞 ↥F) ↥F)ˣ,
    (∃ k : ℕ, x ^ p ^ k ∈ (Units.map (algebraMap ↥F (FiniteAdeleRing (𝓞 ↥F) ↥F) : ↥F →* FiniteAdeleRing (𝓞 ↥F) ↥F)).range ⊔
        IsDedekindDomain.FiniteAdeleRing.unitIdelesOutside (𝓞 ↥F) ↥F (NumberField.placesOverPrimes ↥F (↑S : Set Nat.Primes))) →
    Units.map (Ψ : FiniteAdeleRing (𝓞 ↥F) ↥F →* FiniteAdeleRing (𝓞 ↥F₁) ↥F₁) x ∈
      (Units.map (algebraMap ↥F₁ (FiniteAdeleRing (𝓞 ↥F₁) ↥F₁) : ↥F₁ →* FiniteAdeleRing (𝓞 ↥F₁) ↥F₁)).range ⊔
        IsDedekindDomain.FiniteAdeleRing.unitIdelesOutside (𝓞 ↥F₁) ↥F₁ (NumberField.placesOverPrimes ↥F₁ (↑S : Set Nat.Primes)))

noncomputable abbrev finIdele (K : Type) [Field K] [NumberField K] : (AdeleRing (𝓞 K) K)ˣ →* (FiniteAdeleRing (𝓞 K) K)ˣ :=
  Units.map (RingHom.snd (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)).toMonoidHom

omit [IsGalois ℚ ↥F] in
theorem finIdele_principal (a : (↥F)ˣ) :
    finIdele ↥F (Units.map (algebraMap ↥F (AdeleRing (𝓞 ↥F) ↥F) : ↥F →* AdeleRing (𝓞 ↥F) ↥F) a) =
      Units.map (algebraMap ↥F (FiniteAdeleRing (𝓞 ↥F) ↥F) : ↥F →* FiniteAdeleRing (𝓞 ↥F) ↥F) a :=
  Units.ext rfl

omit [IsGalois ℚ ↥F] in

theorem finIdele_mem_sup_of_mem_sup (T : Set (HeightOneSpectrum (𝓞 ↥F))) (z : (AdeleRing (𝓞 ↥F) ↥F)ˣ)
    (hz : z ∈ principalIdeles (𝓞 ↥F) ↥F ⊔ NumberField.AdeleRing.unitIdelesOutside (𝓞 ↥F) ↥F T) :
    finIdele ↥F z ∈ (Units.map (algebraMap ↥F (FiniteAdeleRing (𝓞 ↥F) ↥F) : ↥F →* FiniteAdeleRing (𝓞 ↥F) ↥F)).range ⊔
      IsDedekindDomain.FiniteAdeleRing.unitIdelesOutside (𝓞 ↥F) ↥F T := by
  have h := Subgroup.mem_map_of_mem (finIdele ↥F) hz
  rw [Subgroup.map_sup] at h
  have hP : (principalIdeles (𝓞 ↥F) ↥F).map (finIdele ↥F) ≤
      (Units.map (algebraMap ↥F (FiniteAdeleRing (𝓞 ↥F) ↥F) : ↥F →* FiniteAdeleRing (𝓞 ↥F) ↥F)).range := by
    rintro _ ⟨s, ⟨a, rfl⟩, rfl⟩
    exact ⟨a, (finIdele_principal F a).symm⟩
  have hU : (NumberField.AdeleRing.unitIdelesOutside (𝓞 ↥F) ↥F T).map (finIdele ↥F) ≤
      IsDedekindDomain.FiniteAdeleRing.unitIdelesOutside (𝓞 ↥F) ↥F T := by
    rintro _ ⟨t, ht, rfl⟩
    exact ht
  exact sup_le_sup hP hU h

omit [IsGalois ℚ ↥F] in

theorem mem_sup_of_finIdele_mem_sup (T : Set (HeightOneSpectrum (𝓞 ↥F))) (y : (AdeleRing (𝓞 ↥F) ↥F)ˣ)
    (hy : finIdele ↥F y ∈ (Units.map (algebraMap ↥F (FiniteAdeleRing (𝓞 ↥F) ↥F) : ↥F →* FiniteAdeleRing (𝓞 ↥F) ↥F)).range ⊔
      IsDedekindDomain.FiniteAdeleRing.unitIdelesOutside (𝓞 ↥F) ↥F T) :
    y ∈ principalIdeles (𝓞 ↥F) ↥F ⊔ NumberField.AdeleRing.unitIdelesOutside (𝓞 ↥F) ↥F T := by
  obtain ⟨s, ⟨a, rfl⟩, t, ht, hst⟩ := Subgroup.mem_sup.1 hy
  set s' : (AdeleRing (𝓞 ↥F) ↥F)ˣ := Units.map (algebraMap ↥F (AdeleRing (𝓞 ↥F) ↥F) : ↥F →* AdeleRing (𝓞 ↥F) ↥F) a with hs'
  refine Subgroup.mem_sup.2 ⟨s', ⟨a, rfl⟩, s'⁻¹ * y, ?_, mul_inv_cancel_left _ _⟩
  show finIdele ↥F (s'⁻¹ * y) ∈ IsDedekindDomain.FiniteAdeleRing.unitIdelesOutside (𝓞 ↥F) ↥F T
  rw [map_mul, map_inv, hs', finIdele_principal, ← hst, inv_mul_cancel_left]
  exact ht

include hJΨ hcapΨ in

theorem jj_mem_sup_of_pow_mem_sup (z : (AdeleRing (𝓞 ↥F) ↥F)ˣ)
    (hz : ∃ k : ℕ, z ^ p ^ k ∈ principalIdeles (𝓞 ↥F) ↥F ⊔ NumberField.AdeleRing.unitIdelesOutside (𝓞 ↥F) ↥F {w | w.under (𝓞 ℚ) ∈ Sq S}) :
    JJ F F₁ J z ∈ principalIdeles (𝓞 ↥F₁) ↥F₁ ⊔ NumberField.AdeleRing.unitIdelesOutside (𝓞 ↥F₁) ↥F₁ {w | w.under (𝓞 ℚ) ∈ Sq S} := by
  have hT : ∀ (K : Type) [Field K] [NumberField K],
      {w : HeightOneSpectrum (𝓞 K) | w.under (𝓞 ℚ) ∈ Sq S} = NumberField.placesOverPrimes K (↑S : Set Nat.Primes) :=
    fun K _ _ => Set.ext fun w => under_mem_Sq_iff S K w
  obtain ⟨k, hk⟩ := hz

  have h1 : (finIdele ↥F z) ^ p ^ k ∈ (Units.map (algebraMap ↥F (FiniteAdeleRing (𝓞 ↥F) ↥F) : ↥F →* FiniteAdeleRing (𝓞 ↥F) ↥F)).range ⊔
      IsDedekindDomain.FiniteAdeleRing.unitIdelesOutside (𝓞 ↥F) ↥F {w | w.under (𝓞 ℚ) ∈ Sq S} := by
    rw [← map_pow]; exact finIdele_mem_sup_of_mem_sup F _ _ hk
  rw [hT ↥F] at h1
  have h2 := hcapΨ (finIdele ↥F z) ⟨k, h1⟩
  rw [← hT ↥F₁] at h2

  have h3 : finIdele ↥F₁ (JJ F F₁ J z) = Units.map (Ψ : FiniteAdeleRing (𝓞 ↥F) ↥F →* FiniteAdeleRing (𝓞 ↥F₁) ↥F₁) (finIdele ↥F z) :=
    Units.ext (hJΨ (z : AdeleRing (𝓞 ↥F) ↥F))
  rw [← h3] at h2
  exact mem_sup_of_finIdele_mem_sup F₁ _ _ h2

end capPsi
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95 P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95.Infl"
end Reduce95
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95 P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95.Infl"

set_option autoImplicit false
open CategoryTheory IsDedekindDomain NumberField

namespace Reduce95
open ExtCitation M4aHerbrand

section psi

variable (S : Finset Nat.Primes) (F F₁ : IntermediateField ℚ (AlgebraicClosure ℚ))
  [NumberField ↥F] [IsGalois ℚ ↥F] [NumberField ↥F₁] [IsGalois ℚ ↥F₁] [hle : Fact (F ≤ F₁)]
  (J : AdeleRing (𝓞 ↥F) ↥F →+* AdeleRing (𝓞 ↥F₁) ↥F₁)
  (hJF : ∀ a : ↥F, J (algebraMap ↥F (AdeleRing (𝓞 ↥F) ↥F) a) = algebraMap ↥F₁ (AdeleRing (𝓞 ↥F₁) ↥F₁) (algebraMap ↥F ↥F₁ a))
  (hJeq : ∀ (g' : ↥F₁ ≃ₐ[ℚ] ↥F₁) (x : AdeleRing (𝓞 ↥F) ↥F), J ((DD F).act (AlgEquiv.restrictNormalHom ↥F g') x) = (DD F₁).act g' (J x))
  (hJout : ∀ (T : Set (HeightOneSpectrum (𝓞 ℚ))) (z : (AdeleRing (𝓞 ↥F) ↥F)ˣ),
    (∀ w : HeightOneSpectrum (𝓞 ↥F), w.under (𝓞 ℚ) ∉ T → finPart w z = 1) →
    ∀ w' : HeightOneSpectrum (𝓞 ↥F₁), w'.under (𝓞 ℚ) ∉ T →
      finPart w' (Units.map (J : AdeleRing (𝓞 ↥F) ↥F →* AdeleRing (𝓞 ↥F₁) ↥F₁) z) = 1)
  (hJunit : ∀ (T : Set (HeightOneSpectrum (𝓞 ℚ))) (z : (AdeleRing (𝓞 ↥F) ↥F)ˣ),
    z ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 ↥F) ↥F {w | w.under (𝓞 ℚ) ∈ T} →
    Units.map (J : AdeleRing (𝓞 ↥F) ↥F →* AdeleRing (𝓞 ↥F₁) ↥F₁) z ∈
      NumberField.AdeleRing.unitIdelesOutside (𝓞 ↥F₁) ↥F₁ {w' | w'.under (𝓞 ℚ) ∈ T})
  (hJinf : ∀ z : (AdeleRing (𝓞 ↥F) ↥F)ˣ, infPart z = 1 → infPart (Units.map (J : AdeleRing (𝓞 ↥F) ↥F →* AdeleRing (𝓞 ↥F₁) ↥F₁) z) = 1)
  (hJcont : Continuous J)
  (hJloc : ∀ (z z' : (AdeleRing (𝓞 ↥F) ↥F)ˣ) (w' : HeightOneSpectrum (𝓞 ↥F₁)),
    finPart (w'.under (𝓞 ↥F)) z = finPart (w'.under (𝓞 ↥F)) z' → finPart w' (JJ F F₁ J z) = finPart w' (JJ F F₁ J z'))

def adele (x : (InfiniteAdeleRing ↥F)) (a : (FiniteAdeleRing (𝓞 ↥F) ↥F)) : (AdeleRing (𝓞 ↥F) ↥F) := (x, a)

omit [IsGalois ℚ ↥F] in
@[scoped simp] theorem adele_fst (x : (InfiniteAdeleRing ↥F)) (a : (FiniteAdeleRing (𝓞 ↥F) ↥F)) : (adele F x a).1 = x := rfl
omit [IsGalois ℚ ↥F] in
@[scoped simp] theorem adele_snd (x : (InfiniteAdeleRing ↥F)) (a : (FiniteAdeleRing (𝓞 ↥F) ↥F)) : (adele F x a).2 = a := rfl
omit [IsGalois ℚ ↥F] in
theorem adele_sub (x x' : (InfiniteAdeleRing ↥F)) (a a' : (FiniteAdeleRing (𝓞 ↥F) ↥F)) : adele F x a - adele F x' a' = adele F (x - x') (a - a') := rfl
omit [IsGalois ℚ ↥F] in
theorem adele_add (x x' : (InfiniteAdeleRing ↥F)) (a a' : (FiniteAdeleRing (𝓞 ↥F) ↥F)) : adele F x a + adele F x' a' = adele F (x + x') (a + a') := rfl
omit [IsGalois ℚ ↥F] in
theorem adele_mul (x x' : (InfiniteAdeleRing ↥F)) (a a' : (FiniteAdeleRing (𝓞 ↥F) ↥F)) : adele F x a * adele F x' a' = adele F (x * x') (a * a') := rfl
omit [IsGalois ℚ ↥F] in
theorem adele_one_one : adele F 1 1 = 1 := rfl
omit [IsGalois ℚ ↥F] in
theorem adele_zero_zero : adele F 0 0 = 0 := rfl
omit [IsGalois ℚ ↥F] in
theorem adele_eta (z : (AdeleRing (𝓞 ↥F) ↥F)) : adele F z.1 z.2 = z := rfl
omit [IsGalois ℚ ↥F] [IsGalois ℚ ↥F₁] in

theorem snd_sub' (z z' : (AdeleRing (𝓞 ↥F₁) ↥F₁)) : (z - z').2 = z.2 - z'.2 := rfl

noncomputable abbrev infIdele (x : (InfiniteAdeleRing ↥F)ˣ) : (AdeleRing (𝓞 ↥F) ↥F)ˣ := MulEquiv.prodUnits.symm (x, 1)

include hJloc in
omit [IsGalois ℚ ↥F] [IsGalois ℚ ↥F₁] in

theorem snd_J_infIdele (x : (InfiniteAdeleRing ↥F)ˣ) : (J (adele F (x : (InfiniteAdeleRing ↥F)) 1)).2 = 1 := by
  have h : ∀ w' : HeightOneSpectrum (𝓞 ↥F₁), finPart w' (JJ F F₁ J (infIdele F x)) = 1 := fun w' => by
    rw [← map_one (finPart w' : (AdeleRing (𝓞 ↥F₁) ↥F₁)ˣ →* _), ← map_one (JJ F F₁ J)]
    exact hJloc _ _ w' (Units.ext rfl)
  apply FiniteAdeleRing.ext
  intro w'
  exact congrArg Units.val (h w')

omit [NumberField ↥F] [IsGalois ℚ ↥F] in

theorem exists_units_sub_eq (y : (InfiniteAdeleRing ↥F)) : ∃ u₁ u₂ : (InfiniteAdeleRing ↥F)ˣ, (u₁ : (InfiniteAdeleRing ↥F)) - u₂ = y := by
  classical
  let c : (InfiniteAdeleRing ↥F) := fun v => if y v + 1 = 0 then 2 else 1
  have hcz : ∀ v : InfinitePlace ↥F, CharZero v.Completion := fun v =>
    charZero_of_injective_algebraMap (algebraMap ↥F v.Completion).injective
  have hc : ∀ v, c v ≠ 0 := fun v => by
    show (if y v + 1 = 0 then (2 : v.Completion) else 1) ≠ 0
    haveI := hcz v
    split_ifs
    · exact two_ne_zero
    · exact one_ne_zero
  have hyc : ∀ v, y v + c v ≠ 0 := fun v => by
    show y v + (if y v + 1 = 0 then (2 : v.Completion) else 1) ≠ 0
    split_ifs with h
    · intro h2
      have : (1 : v.Completion) = 0 := by
        have e : y v + 2 - (y v + 1) = 1 := by ring
        rw [← e, h2, h, sub_zero]
      exact one_ne_zero this
    · exact h
  have hu₂ : IsUnit c := isUnit_iff_exists_inv.2 ⟨fun v => (c v)⁻¹, funext fun v => mul_inv_cancel₀ (hc v)⟩
  have hu₁ : IsUnit (y + c) := isUnit_iff_exists_inv.2 ⟨fun v => (y v + c v)⁻¹, funext fun v => mul_inv_cancel₀ (hyc v)⟩
  exact ⟨hu₁.unit, hu₂.unit, by rw [IsUnit.unit_spec, IsUnit.unit_spec, add_sub_cancel_right]⟩

include hJloc in
omit [IsGalois ℚ ↥F] [IsGalois ℚ ↥F₁] in

theorem snd_J_inl (y : (InfiniteAdeleRing ↥F)) : (J (adele F y 0)).2 = 0 := by
  have key : ∀ u : (InfiniteAdeleRing ↥F)ˣ, (J (adele F ((u : (InfiniteAdeleRing ↥F)) - 1) 0)).2 = 0 := fun u => by
    have e : adele F ((u : (InfiniteAdeleRing ↥F)) - 1) 0 = adele F (u : (InfiniteAdeleRing ↥F)) 1 - adele F ((1 : (InfiniteAdeleRing ↥F)ˣ) : (InfiniteAdeleRing ↥F)) 1 := by
      rw [adele_sub, Units.val_one, sub_self]
    rw [e, map_sub, snd_sub', snd_J_infIdele F F₁ J hJloc u, snd_J_infIdele F F₁ J hJloc 1, sub_self]
  obtain ⟨u₁, u₂, rfl⟩ := exists_units_sub_eq F y
  have e : adele F ((u₁ : (InfiniteAdeleRing ↥F)) - u₂) 0 = adele F ((u₁ : (InfiniteAdeleRing ↥F)) - 1) 0 - adele F ((u₂ : (InfiniteAdeleRing ↥F)) - 1) 0 := by
    rw [adele_sub, sub_sub_sub_cancel_right, sub_self]
  rw [e, map_sub, snd_sub', key, key, sub_self]

noncomputable def Psi : (FiniteAdeleRing (𝓞 ↥F) ↥F) →+* (FiniteAdeleRing (𝓞 ↥F₁) ↥F₁) where
  toFun a := (J (adele F 0 a)).2
  map_one' := by
    have e : adele F 0 1 = adele F 1 1 - adele F 1 0 := by rw [adele_sub, sub_self, sub_zero]
    rw [e, map_sub, snd_sub', adele_one_one, map_one, snd_J_inl F F₁ J hJloc, sub_zero]
    rfl
  map_mul' a b := by
    have e : adele F 0 (a * b) = adele F 0 a * adele F 0 b := by rw [adele_mul, mul_zero]
    rw [e, map_mul]
    rfl
  map_zero' := by rw [adele_zero_zero, map_zero]; rfl
  map_add' a b := by
    have e : adele F 0 (a + b) = adele F 0 a + adele F 0 b := by rw [adele_add, add_zero]
    rw [e, map_add]
    rfl

theorem Psi_apply (a : (FiniteAdeleRing (𝓞 ↥F) ↥F)) : Psi F F₁ J hJloc a = (J (adele F 0 a)).2 := rfl

include hJloc in

theorem snd_J_eq_Psi (z : (AdeleRing (𝓞 ↥F) ↥F)) : (J z).2 = Psi F F₁ J hJloc z.2 := by
  have e : z = adele F z.1 0 + adele F 0 z.2 := by rw [adele_add, add_zero, zero_add, adele_eta]
  conv_lhs => rw [e]
  rw [map_add, Psi_apply]
  change (J (adele F z.1 0)).2 + (J (adele F 0 z.2)).2 = _
  rw [snd_J_inl F F₁ J hJloc, zero_add]

include hJcont in

theorem continuous_Psi : Continuous (Psi F F₁ J hJloc) := by
  show Continuous fun a : (FiniteAdeleRing (𝓞 ↥F) ↥F) => (J (adele F 0 a)).2
  exact continuous_snd.comp (hJcont.comp (continuous_const.prodMk continuous_id))

include hJF hJloc in

theorem Psi_algebraMap (a : ↥F) :
    Psi F F₁ J hJloc (algebraMap ↥F (FiniteAdeleRing (𝓞 ↥F) ↥F) a) = algebraMap ↥F₁ (FiniteAdeleRing (𝓞 ↥F₁) ↥F₁) (IntermediateField.inclusion hle.out a) := by
  have h := snd_J_eq_Psi F F₁ J hJloc (algebraMap ↥F (AdeleRing (𝓞 ↥F) ↥F) a)
  rw [hJF] at h
  exact h.symm

end psi
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95 P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95.Infl"
end Reduce95
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95 P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95.Infl"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
open CategoryTheory IsDedekindDomain NumberField

namespace Reduce95
open ExtCitation groupCohomology GroupCohomology M4aHerbrand

section generic

variable {G G₁ G₂ : Type} [Group G] [Group G₁] [Group G₂] (π : G₁ →* G) (π' : G₂ →* G₁)

theorem pasteSq' {X X' : Rep ℤ G} {X₁ X₁' : Rep ℤ G₁} {X₂ X₂' : Rep ℤ G₂} (u : X ⟶ X') (u₁ : X₁ ⟶ X₁') (u₂ : X₂ ⟶ X₂')
    (jX : Rep.res π X ⟶ X₁) (jX'1 : Rep.res π X' ⟶ X₁') (kX : Rep.res π' X₁ ⟶ X₂) (kX' : Rep.res π' X₁' ⟶ X₂')
    (hsq : (Rep.resFunctor π).map u ≫ jX'1 = jX ≫ u₁) (hsq' : (Rep.resFunctor π').map u₁ ≫ kX' = kX ≫ u₂) :
    (Rep.resFunctor (π.comp π')).map u ≫ ((Rep.resFunctor π').map jX'1 ≫ kX' : Rep.res (π.comp π') X' ⟶ X₂') =
      ((Rep.resFunctor π').map jX ≫ kX : Rep.res (π.comp π') X ⟶ X₂) ≫ u₂ := by
  apply Rep.hom_ext; apply DFunLike.ext; intro x
  change kX'.hom (jX'1.hom (u.hom x)) = u₂.hom (kX.hom (jX.hom x))
  have h1 := congrArg (fun φ => φ.hom x) hsq
  have h2 := congrArg (fun φ => φ.hom (jX.hom x)) hsq'
  change jX'1.hom (u.hom x) = u₁.hom (jX.hom x) at h1
  change kX'.hom (u₁.hom (jX.hom x)) = u₂.hom (kX.hom (jX.hom x)) at h2
  rw [h1, h2]

variable (p : ℕ) {X : Rep ℤ G} {X₁ : Rep ℤ G₁} {X₂ : Rep ℤ G₂} (φ : Rep.res π X ⟶ X₁) (φ' : Rep.res π' X₁ ⟶ X₂)

theorem hpit_comp_of_left (h : ∀ c : X, (∃ k : ℕ, p ^ k • c = 0) → φ.hom c = 0) :
    ∀ c : X, (∃ k : ℕ, p ^ k • c = 0) → ((Rep.resFunctor π').map φ ≫ φ' : Rep.res (π.comp π') X ⟶ X₂).hom c = 0 := by
  intro c hc
  change φ'.hom (φ.hom c) = 0
  rw [h c hc, map_zero]

theorem hpit_comp_of_right (h' : ∀ c₁ : X₁, (∃ k : ℕ, p ^ k • c₁ = 0) → φ'.hom c₁ = 0) :
    ∀ c : X, (∃ k : ℕ, p ^ k • c = 0) → ((Rep.resFunctor π').map φ ≫ φ' : Rep.res (π.comp π') X ⟶ X₂).hom c = 0 := by
  rintro c ⟨k, hk⟩
  change φ'.hom (φ.hom c) = 0
  refine h' _ ⟨k, ?_⟩
  rw [← map_nsmul, hk, map_zero]

end generic
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95 P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95.Infl"

section hjEComp

variable (S : Finset Nat.Primes) (F F₁ F₂ : IntermediateField ℚ (AlgebraicClosure ℚ))
  [NumberField ↥F] [IsGalois ℚ ↥F] [NumberField ↥F₁] [IsGalois ℚ ↥F₁] [NumberField ↥F₂] [IsGalois ℚ ↥F₂]
  {π : (↥F₁ ≃ₐ[ℚ] ↥F₁) →* (↥F ≃ₐ[ℚ] ↥F)} {π' : (↥F₂ ≃ₐ[ℚ] ↥F₂) →* (↥F₁ ≃ₐ[ℚ] ↥F₁)}
  (jE : Rep.res π (seqF S F).X₁ ⟶ (seqF S F₁).X₁) (jE' : Rep.res π' (seqF S F₁).X₁ ⟶ (seqF S F₂).X₁)
  (hjE : ∀ x, iotaE F₁ (Sq S) (jE.hom x) = iotaE F (Sq S) x) (hjE' : ∀ x, iotaE F₂ (Sq S) (jE'.hom x) = iotaE F₁ (Sq S) x)

include hjE hjE' in
theorem hjE_comp (x : (seqF S F).X₁) :
    iotaE F₂ (Sq S) (((Rep.resFunctor π').map jE ≫ jE' : Rep.res (π.comp π') (seqF S F).X₁ ⟶ (seqF S F₂).X₁).hom x) =
      iotaE F (Sq S) x := by
  change iotaE F₂ (Sq S) (jE'.hom (jE.hom x)) = _
  rw [hjE', hjE]

end hjEComp
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95 P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95.Infl"

section hexfComp

variable {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes)
  (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) [FiniteDimensional (ZMod p) M]
  (F F₁ F₂ : IntermediateField ℚ (AlgebraicClosure ℚ))
  [NumberField ↥F] [IsGalois ℚ ↥F] [NumberField ↥F₁] [IsGalois ℚ ↥F₁] [NumberField ↥F₂] [IsGalois ℚ ↥F₂]
  (hunr₂ : ∀ w : HeightOneSpectrum (𝓞 ↥F₂), w ∉ TT S F₂ → Ideal.ramificationIdx' (w.asIdeal.under (𝓞 ℚ)) w.asIdeal = 1)
  (sys₂ : InvSys F₂)
  (π : (↥F₁ ≃ₐ[ℚ] ↥F₁) →* (↥F ≃ₐ[ℚ] ↥F)) (π' : (↥F₂ ≃ₐ[ℚ] ↥F₂) →* (↥F₁ ≃ₐ[ℚ] ↥F₁))
  (hπ' : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, π' (AlgEquiv.restrictNormalHom ↥F₂ σ) = AlgEquiv.restrictNormalHom ↥F₁ σ)
  (jC : Rep.res π (CS S F) ⟶ CS S F₁) (jC' : Rep.res π' (CS S F₁) ⟶ CS S F₂)
  (hsep : SepClause S F₁ F₂ (Bofπ F M π))
  (u : ℕ) (hu : ∀ a : ZMod p, u • a = 0 → a = 0)

set_option maxHeartbeats 3200000 in
include hπ' hsep hu in

theorem hEXF_comp (φ : Rep.relationModuleInt (Bof M F) ⟶ CS S F) :
    (∃ χ : Rep.free ℤ (↥F₂ ≃ₐ[ℚ] ↥F₂) (Bofπ F M (π.comp π')) ⟶ CS S F₂,
        Infl.inflHom (π.comp π') (Bof M F) ((Rep.resFunctor π').map jC ≫ jC' : Rep.res (π.comp π') (CS S F) ⟶ CS S F₂) φ =
          Rep.relationModuleInt.ι (Bofπ F M (π.comp π')) ≫ χ) ∨
    (∃ x : ↥(groupCohomology (Bofπ F M (π.comp π')) 1),
        (u • alFs S F₂ hunr₂ sys₂ (Bofπ F M (π.comp π')) (Bofπ_torsion F M (π.comp π')))
          (Infl.inflHom (π.comp π') (Bof M F) ((Rep.resFunctor π').map jC ≫ jC' : Rep.res (π.comp π') (CS S F) ⟶ CS S F₂) φ) x ≠ 0) := by
  have htrans : Infl.inflHom (π.comp π') (Bof M F) ((Rep.resFunctor π').map jC ≫ jC' : Rep.res (π.comp π') (CS S F) ⟶ CS S F₂) φ =
      Infl.inflHom π' (Bofπ F M π) jC' (Infl.inflHom π (Bof M F) jC φ) :=
    (Infl.inflHom_comp_inflHom π (Bof M F) π' jC jC' φ).symm
  rw [htrans]
  rcases hsep π' hπ' (DD F₂) (DD_stab S F₂) (fun _ _ => rfl) jC' (hX' F₂ (Bofπ F M (π.comp π')))
      (Infl.inflHom π (Bof M F) jC φ) with ⟨χ, hχ⟩ | ⟨y, hy⟩
  · refine Or.inl ⟨χ, ?_⟩
    rw [Infl.inflHom_apply π' (Bofπ F M π) jC']
    exact hχ.symm
  · refine Or.inr ⟨y, fun h0 => hy ?_⟩
    have h1 : alFs S F₂ hunr₂ sys₂ (Bofπ F M (π.comp π')) (Bofπ_torsion F M (π.comp π'))
        (Infl.inflHom π' (Bofπ F M π) jC' (Infl.inflHom π (Bof M F) jC φ)) y = 0 := hu _ h0
    have h2 := (alFs_eq_zero_iff S F₂ hunr₂ sys₂ (Bofπ F M (π.comp π')) (Bofπ_torsion F M (π.comp π')) _ y).1 h1
    exact h2

end hexfComp
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95 P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95.Infl"

section pitComp

variable {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes)

theorem hcap_of_capClause (F F₁ : IntermediateField ℚ (AlgebraicClosure ℚ))
    [NumberField ↥F] [IsGalois ℚ ↥F] [NumberField ↥F₁] [IsGalois ℚ ↥F₁] [hle : Fact (F ≤ F₁)]
  (J : AdeleRing (𝓞 ↥F) ↥F →+* AdeleRing (𝓞 ↥F₁) ↥F₁)
  (hJF : ∀ a : ↥F, J (algebraMap ↥F (AdeleRing (𝓞 ↥F) ↥F) a) = algebraMap ↥F₁ (AdeleRing (𝓞 ↥F₁) ↥F₁) (algebraMap ↥F ↥F₁ a))
  (hJeq : ∀ (g' : ↥F₁ ≃ₐ[ℚ] ↥F₁) (x : AdeleRing (𝓞 ↥F) ↥F), J ((DD F).act (AlgEquiv.restrictNormalHom ↥F g') x) = (DD F₁).act g' (J x))
  (hJout : ∀ (T : Set (HeightOneSpectrum (𝓞 ℚ))) (z : (AdeleRing (𝓞 ↥F) ↥F)ˣ),
    (∀ w : HeightOneSpectrum (𝓞 ↥F), w.under (𝓞 ℚ) ∉ T → finPart w z = 1) →
    ∀ w' : HeightOneSpectrum (𝓞 ↥F₁), w'.under (𝓞 ℚ) ∉ T →
      finPart w' (Units.map (J : AdeleRing (𝓞 ↥F) ↥F →* AdeleRing (𝓞 ↥F₁) ↥F₁) z) = 1)
  (hJunit : ∀ (T : Set (HeightOneSpectrum (𝓞 ℚ))) (z : (AdeleRing (𝓞 ↥F) ↥F)ˣ),
    z ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 ↥F) ↥F {w | w.under (𝓞 ℚ) ∈ T} →
    Units.map (J : AdeleRing (𝓞 ↥F) ↥F →* AdeleRing (𝓞 ↥F₁) ↥F₁) z ∈
      NumberField.AdeleRing.unitIdelesOutside (𝓞 ↥F₁) ↥F₁ {w' | w'.under (𝓞 ℚ) ∈ T})
  (hJinf : ∀ z : (AdeleRing (𝓞 ↥F) ↥F)ˣ, infPart z = 1 → infPart (Units.map (J : AdeleRing (𝓞 ↥F) ↥F →* AdeleRing (𝓞 ↥F₁) ↥F₁) z) = 1)
  (hJcont : Continuous J)
  (hJloc : ∀ (z z' : (AdeleRing (𝓞 ↥F) ↥F)ˣ) (w' : HeightOneSpectrum (𝓞 ↥F₁)),
    finPart (w'.under (𝓞 ↥F)) z = finPart (w'.under (𝓞 ↥F)) z' → finPart w' (JJ F F₁ J z) = finPart w' (JJ F F₁ J z'))
    (hCAP : CapClause (p := p) S F F₁) :
    ∀ z : (AdeleRing (𝓞 ↥F) ↥F)ˣ,
      (∃ k : ℕ, z ^ p ^ k ∈ principalIdeles (𝓞 ↥F) ↥F ⊔ NumberField.AdeleRing.unitIdelesOutside (𝓞 ↥F) ↥F {w | w.under (𝓞 ℚ) ∈ Sq S}) →
      JJ F F₁ J z ∈ principalIdeles (𝓞 ↥F₁) ↥F₁ ⊔ NumberField.AdeleRing.unitIdelesOutside (𝓞 ↥F₁) ↥F₁ {w | w.under (𝓞 ℚ) ∈ Sq S} :=
  fun z hz => jj_mem_sup_of_pow_mem_sup (S := S) (F := F) (F₁ := F₁) (J := J) (Ψ := Psi F F₁ J hJloc)
    (hJΨ := snd_J_eq_Psi F F₁ J hJloc)
    (hcapΨ := fun x hx => hCAP hle.out (Psi F F₁ J hJloc) (continuous_Psi F F₁ J hJcont hJloc) (Psi_algebraMap F F₁ J hJF hJloc) x hx)
    z hz

set_option maxHeartbeats 6400000 in

theorem hPITco_comp (F Fc F₁ : IntermediateField ℚ (AlgebraicClosure ℚ))
    [NumberField ↥F] [IsGalois ℚ ↥F] [NumberField ↥Fc] [IsGalois ℚ ↥Fc] [NumberField ↥F₁] [IsGalois ℚ ↥F₁]
    [hle_a : Fact (F ≤ Fc)] [hle_b : Fact (Fc ≤ F₁)]
  (Ja : AdeleRing (𝓞 ↥F) ↥F →+* AdeleRing (𝓞 ↥Fc) ↥Fc)
  (hJF_a : ∀ a : ↥F, Ja (algebraMap ↥F (AdeleRing (𝓞 ↥F) ↥F) a) = algebraMap ↥Fc (AdeleRing (𝓞 ↥Fc) ↥Fc) (algebraMap ↥F ↥Fc a))
  (hJeq_a : ∀ (g' : ↥Fc ≃ₐ[ℚ] ↥Fc) (x : AdeleRing (𝓞 ↥F) ↥F), Ja ((DD F).act (AlgEquiv.restrictNormalHom ↥F g') x) = (DD Fc).act g' (Ja x))
  (hJout_a : ∀ (T : Set (HeightOneSpectrum (𝓞 ℚ))) (z : (AdeleRing (𝓞 ↥F) ↥F)ˣ),
    (∀ w : HeightOneSpectrum (𝓞 ↥F), w.under (𝓞 ℚ) ∉ T → finPart w z = 1) →
    ∀ w' : HeightOneSpectrum (𝓞 ↥Fc), w'.under (𝓞 ℚ) ∉ T →
      finPart w' (Units.map (Ja : AdeleRing (𝓞 ↥F) ↥F →* AdeleRing (𝓞 ↥Fc) ↥Fc) z) = 1)
  (hJunit_a : ∀ (T : Set (HeightOneSpectrum (𝓞 ℚ))) (z : (AdeleRing (𝓞 ↥F) ↥F)ˣ),
    z ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 ↥F) ↥F {w | w.under (𝓞 ℚ) ∈ T} →
    Units.map (Ja : AdeleRing (𝓞 ↥F) ↥F →* AdeleRing (𝓞 ↥Fc) ↥Fc) z ∈
      NumberField.AdeleRing.unitIdelesOutside (𝓞 ↥Fc) ↥Fc {w' | w'.under (𝓞 ℚ) ∈ T})
  (hJinf_a : ∀ z : (AdeleRing (𝓞 ↥F) ↥F)ˣ, infPart z = 1 → infPart (Units.map (Ja : AdeleRing (𝓞 ↥F) ↥F →* AdeleRing (𝓞 ↥Fc) ↥Fc) z) = 1)
  (hJcont_a : Continuous Ja)
  (hJloc_a : ∀ (z z' : (AdeleRing (𝓞 ↥F) ↥F)ˣ) (w' : HeightOneSpectrum (𝓞 ↥Fc)),
    finPart (w'.under (𝓞 ↥F)) z = finPart (w'.under (𝓞 ↥F)) z' → finPart w' (JJ F Fc Ja z) = finPart w' (JJ F Fc Ja z'))
  (Jb : AdeleRing (𝓞 ↥Fc) ↥Fc →+* AdeleRing (𝓞 ↥F₁) ↥F₁)
  (hJF_b : ∀ a : ↥Fc, Jb (algebraMap ↥Fc (AdeleRing (𝓞 ↥Fc) ↥Fc) a) = algebraMap ↥F₁ (AdeleRing (𝓞 ↥F₁) ↥F₁) (algebraMap ↥Fc ↥F₁ a))
  (hJeq_b : ∀ (g' : ↥F₁ ≃ₐ[ℚ] ↥F₁) (x : AdeleRing (𝓞 ↥Fc) ↥Fc), Jb ((DD Fc).act (AlgEquiv.restrictNormalHom ↥Fc g') x) = (DD F₁).act g' (Jb x))
  (hJout_b : ∀ (T : Set (HeightOneSpectrum (𝓞 ℚ))) (z : (AdeleRing (𝓞 ↥Fc) ↥Fc)ˣ),
    (∀ w : HeightOneSpectrum (𝓞 ↥Fc), w.under (𝓞 ℚ) ∉ T → finPart w z = 1) →
    ∀ w' : HeightOneSpectrum (𝓞 ↥F₁), w'.under (𝓞 ℚ) ∉ T →
      finPart w' (Units.map (Jb : AdeleRing (𝓞 ↥Fc) ↥Fc →* AdeleRing (𝓞 ↥F₁) ↥F₁) z) = 1)
  (hJunit_b : ∀ (T : Set (HeightOneSpectrum (𝓞 ℚ))) (z : (AdeleRing (𝓞 ↥Fc) ↥Fc)ˣ),
    z ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 ↥Fc) ↥Fc {w | w.under (𝓞 ℚ) ∈ T} →
    Units.map (Jb : AdeleRing (𝓞 ↥Fc) ↥Fc →* AdeleRing (𝓞 ↥F₁) ↥F₁) z ∈
      NumberField.AdeleRing.unitIdelesOutside (𝓞 ↥F₁) ↥F₁ {w' | w'.under (𝓞 ℚ) ∈ T})
  (hJinf_b : ∀ z : (AdeleRing (𝓞 ↥Fc) ↥Fc)ˣ, infPart z = 1 → infPart (Units.map (Jb : AdeleRing (𝓞 ↥Fc) ↥Fc →* AdeleRing (𝓞 ↥F₁) ↥F₁) z) = 1)
    (hCAP_a : CapClause (p := p) S F Fc)
    (B : Rep ℤ (↥F ≃ₐ[ℚ] ↥F)) [Fintype B] (hB : ∀ b : B, p • b = 0)
    (φ : Rep.relationModuleInt B ⟶ CS S F) :
    ∃ (t : Rep.relationModuleInt (Rep.res ((levelMapR F Fc hle_a.out).comp (levelMapR Fc F₁ hle_b.out)) B) ⟶ (seqF S F₁).X₃)
      (χ : Rep.free ℤ (↥F₁ ≃ₐ[ℚ] ↥F₁) (Rep.res ((levelMapR F Fc hle_a.out).comp (levelMapR Fc F₁ hle_b.out)) B) ⟶ CS S F₁),
      Infl.inflHom ((levelMapR F Fc hle_a.out).comp (levelMapR Fc F₁ hle_b.out)) B
          ((Rep.resFunctor (levelMapR Fc F₁ hle_b.out)).map (jC S F Fc Ja hJF_a hJeq_a hJout_a hJunit_a hJinf_a) ≫
              jC S Fc F₁ Jb hJF_b hJeq_b hJout_b hJunit_b hJinf_b :
            Rep.res ((levelMapR F Fc hle_a.out).comp (levelMapR Fc F₁ hle_b.out)) (CS S F) ⟶ CS S F₁) φ =
        t ≫ GroupCohomology.RepImage.ι (LF S F₁) +
          Rep.relationModuleInt.ι (Rep.res ((levelMapR F Fc hle_a.out).comp (levelMapR Fc F₁ hle_b.out)) B) ≫ χ := by
  haveI : Fintype (↥F ≃ₐ[ℚ] ↥F) := Fintype.ofFinite _
  haveI : Fintype (↥F₁ ≃ₐ[ℚ] ↥F₁) := Fintype.ofFinite _
  haveI : Finite (GroupCohomology.RepImage.seq (LF S F)).X₃ := finite_repCokernel_LF S F
  haveI : Finite (GroupCohomology.RepImage.seq (LF S F₁)).X₃ := finite_repCokernel_LF S F₁
  exact hPITco_gen ((levelMapR F Fc hle_a.out).comp (levelMapR Fc F₁ hle_b.out)) B p hB (hTcl S F) (hTcl S F₁)
    ((Rep.resFunctor (levelMapR Fc F₁ hle_b.out)).map (jY S F Fc Ja hJF_a hJeq_a hJout_a hJunit_a hJinf_a) ≫
      jY S Fc F₁ Jb hJF_b hJeq_b hJout_b hJunit_b hJinf_b)
    ((Rep.resFunctor (levelMapR Fc F₁ hle_b.out)).map (jC S F Fc Ja hJF_a hJeq_a hJout_a hJunit_a hJinf_a) ≫
      jC S Fc F₁ Jb hJF_b hJeq_b hJout_b hJunit_b hJinf_b)
    ((Rep.resFunctor (levelMapR Fc F₁ hle_b.out)).map (jCl S F Fc Ja hJF_a hJeq_a hJout_a hJunit_a hJinf_a) ≫
      jCl S Fc F₁ Jb hJF_b hJeq_b hJout_b hJunit_b hJinf_b)
    (pasteSq' (levelMapR F Fc hle_a.out) (levelMapR Fc F₁ hle_b.out)
      (GroupCohomology.RepImage.ι (LF S F)) (GroupCohomology.RepImage.ι (LF S Fc)) (GroupCohomology.RepImage.ι (LF S F₁))
      (jY S F Fc Ja hJF_a hJeq_a hJout_a hJunit_a hJinf_a) (jC S F Fc Ja hJF_a hJeq_a hJout_a hJunit_a hJinf_a)
      (jY S Fc F₁ Jb hJF_b hJeq_b hJout_b hJunit_b hJinf_b) (jC S Fc F₁ Jb hJF_b hJeq_b hJout_b hJunit_b hJinf_b)
      (hsqCι S F Fc Ja hJF_a hJeq_a hJout_a hJunit_a hJinf_a) (hsqCι S Fc F₁ Jb hJF_b hJeq_b hJout_b hJunit_b hJinf_b))
    (pasteSq' (levelMapR F Fc hle_a.out) (levelMapR Fc F₁ hle_b.out)
      (GroupCohomology.RepImage.seq (LF S F)).g (GroupCohomology.RepImage.seq (LF S Fc)).g (GroupCohomology.RepImage.seq (LF S F₁)).g
      (jC S F Fc Ja hJF_a hJeq_a hJout_a hJunit_a hJinf_a) (jCl S F Fc Ja hJF_a hJeq_a hJout_a hJunit_a hJinf_a)
      (jC S Fc F₁ Jb hJF_b hJeq_b hJout_b hJunit_b hJinf_b) (jCl S Fc F₁ Jb hJF_b hJeq_b hJout_b hJunit_b hJinf_b)
      (hsqCl S F Fc Ja hJF_a hJeq_a hJout_a hJunit_a hJinf_a) (hsqCl S Fc F₁ Jb hJF_b hJeq_b hJout_b hJunit_b hJinf_b))
    (hpit_comp_of_left (levelMapR F Fc hle_a.out) (levelMapR Fc F₁ hle_b.out) p
      (jCl S F Fc Ja hJF_a hJeq_a hJout_a hJunit_a hJinf_a) (jCl S Fc F₁ Jb hJF_b hJeq_b hJout_b hJunit_b hJinf_b)
      (hpit_of_cap S F Fc Ja hJF_a hJeq_a hJout_a hJunit_a hJinf_a p
        (hcap_of_capClause S F Fc Ja hJF_a hJeq_a hJout_a hJunit_a hJinf_a hJcont_a hJloc_a hCAP_a)))
    (Infl.inflHom ((levelMapR F Fc hle_a.out).comp (levelMapR Fc F₁ hle_b.out)) B
      ((Rep.resFunctor (levelMapR Fc F₁ hle_b.out)).map (jC S F Fc Ja hJF_a hJeq_a hJout_a hJunit_a hJinf_a) ≫
        jC S Fc F₁ Jb hJF_b hJeq_b hJout_b hJunit_b hJinf_b))
    (fun _ => rfl) φ

set_option maxHeartbeats 6400000 in

theorem hPITker_comp (F₁ K F₂ : IntermediateField ℚ (AlgebraicClosure ℚ))
    [NumberField ↥F₁] [IsGalois ℚ ↥F₁] [NumberField ↥K] [IsGalois ℚ ↥K] [NumberField ↥F₂] [IsGalois ℚ ↥F₂]
    [hle_c : Fact (F₁ ≤ K)] [hle_d : Fact (K ≤ F₂)]
  (Jc : AdeleRing (𝓞 ↥F₁) ↥F₁ →+* AdeleRing (𝓞 ↥K) ↥K)
  (hJF_c : ∀ a : ↥F₁, Jc (algebraMap ↥F₁ (AdeleRing (𝓞 ↥F₁) ↥F₁) a) = algebraMap ↥K (AdeleRing (𝓞 ↥K) ↥K) (algebraMap ↥F₁ ↥K a))
  (hJeq_c : ∀ (g' : ↥K ≃ₐ[ℚ] ↥K) (x : AdeleRing (𝓞 ↥F₁) ↥F₁), Jc ((DD F₁).act (AlgEquiv.restrictNormalHom ↥F₁ g') x) = (DD K).act g' (Jc x))
  (hJout_c : ∀ (T : Set (HeightOneSpectrum (𝓞 ℚ))) (z : (AdeleRing (𝓞 ↥F₁) ↥F₁)ˣ),
    (∀ w : HeightOneSpectrum (𝓞 ↥F₁), w.under (𝓞 ℚ) ∉ T → finPart w z = 1) →
    ∀ w' : HeightOneSpectrum (𝓞 ↥K), w'.under (𝓞 ℚ) ∉ T →
      finPart w' (Units.map (Jc : AdeleRing (𝓞 ↥F₁) ↥F₁ →* AdeleRing (𝓞 ↥K) ↥K) z) = 1)
  (hJunit_c : ∀ (T : Set (HeightOneSpectrum (𝓞 ℚ))) (z : (AdeleRing (𝓞 ↥F₁) ↥F₁)ˣ),
    z ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 ↥F₁) ↥F₁ {w | w.under (𝓞 ℚ) ∈ T} →
    Units.map (Jc : AdeleRing (𝓞 ↥F₁) ↥F₁ →* AdeleRing (𝓞 ↥K) ↥K) z ∈
      NumberField.AdeleRing.unitIdelesOutside (𝓞 ↥K) ↥K {w' | w'.under (𝓞 ℚ) ∈ T})
  (hJinf_c : ∀ z : (AdeleRing (𝓞 ↥F₁) ↥F₁)ˣ, infPart z = 1 → infPart (Units.map (Jc : AdeleRing (𝓞 ↥F₁) ↥F₁ →* AdeleRing (𝓞 ↥K) ↥K) z) = 1)
  (Jd : AdeleRing (𝓞 ↥K) ↥K →+* AdeleRing (𝓞 ↥F₂) ↥F₂)
  (hJF_d : ∀ a : ↥K, Jd (algebraMap ↥K (AdeleRing (𝓞 ↥K) ↥K) a) = algebraMap ↥F₂ (AdeleRing (𝓞 ↥F₂) ↥F₂) (algebraMap ↥K ↥F₂ a))
  (hJeq_d : ∀ (g' : ↥F₂ ≃ₐ[ℚ] ↥F₂) (x : AdeleRing (𝓞 ↥K) ↥K), Jd ((DD K).act (AlgEquiv.restrictNormalHom ↥K g') x) = (DD F₂).act g' (Jd x))
  (hJout_d : ∀ (T : Set (HeightOneSpectrum (𝓞 ℚ))) (z : (AdeleRing (𝓞 ↥K) ↥K)ˣ),
    (∀ w : HeightOneSpectrum (𝓞 ↥K), w.under (𝓞 ℚ) ∉ T → finPart w z = 1) →
    ∀ w' : HeightOneSpectrum (𝓞 ↥F₂), w'.under (𝓞 ℚ) ∉ T →
      finPart w' (Units.map (Jd : AdeleRing (𝓞 ↥K) ↥K →* AdeleRing (𝓞 ↥F₂) ↥F₂) z) = 1)
  (hJunit_d : ∀ (T : Set (HeightOneSpectrum (𝓞 ℚ))) (z : (AdeleRing (𝓞 ↥K) ↥K)ˣ),
    z ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 ↥K) ↥K {w | w.under (𝓞 ℚ) ∈ T} →
    Units.map (Jd : AdeleRing (𝓞 ↥K) ↥K →* AdeleRing (𝓞 ↥F₂) ↥F₂) z ∈
      NumberField.AdeleRing.unitIdelesOutside (𝓞 ↥F₂) ↥F₂ {w' | w'.under (𝓞 ℚ) ∈ T})
  (hJinf_d : ∀ z : (AdeleRing (𝓞 ↥K) ↥K)ˣ, infPart z = 1 → infPart (Units.map (Jd : AdeleRing (𝓞 ↥K) ↥K →* AdeleRing (𝓞 ↥F₂) ↥F₂) z) = 1)
  (hJcont_d : Continuous Jd)
  (hJloc_d : ∀ (z z' : (AdeleRing (𝓞 ↥K) ↥K)ˣ) (w' : HeightOneSpectrum (𝓞 ↥F₂)),
    finPart (w'.under (𝓞 ↥K)) z = finPart (w'.under (𝓞 ↥K)) z' → finPart w' (JJ K F₂ Jd z) = finPart w' (JJ K F₂ Jd z'))
    (hCAP_d : CapClause (p := p) S K F₂)
    (B : Rep ℤ (↥F₁ ≃ₐ[ℚ] ↥F₁)) [Fintype B] (hB : ∀ b : B, p • b = 0)
    (t : Rep.relationModuleInt B ⟶ (seqF S F₁).X₃) (χ : Rep.free ℤ (↥F₁ ≃ₐ[ℚ] ↥F₁) B ⟶ CS S F₁)
    (h : t ≫ GroupCohomology.RepImage.ι (LF S F₁) = Rep.relationModuleInt.ι B ≫ χ) :
    ∃ χ' : Rep.free ℤ (↥F₂ ≃ₐ[ℚ] ↥F₂) (Rep.res ((levelMapR F₁ K hle_c.out).comp (levelMapR K F₂ hle_d.out)) B) ⟶ (seqF S F₂).X₃,
      Infl.inflHom ((levelMapR F₁ K hle_c.out).comp (levelMapR K F₂ hle_d.out)) B
          ((Rep.resFunctor (levelMapR K F₂ hle_d.out)).map (jY S F₁ K Jc hJF_c hJeq_c hJout_c hJunit_c hJinf_c) ≫
              jY S K F₂ Jd hJF_d hJeq_d hJout_d hJunit_d hJinf_d :
            Rep.res ((levelMapR F₁ K hle_c.out).comp (levelMapR K F₂ hle_d.out)) (seqF S F₁).X₃ ⟶ (seqF S F₂).X₃) t =
        Rep.relationModuleInt.ι (Rep.res ((levelMapR F₁ K hle_c.out).comp (levelMapR K F₂ hle_d.out)) B) ≫ χ' := by
  haveI : Fintype (↥F₁ ≃ₐ[ℚ] ↥F₁) := Fintype.ofFinite _
  haveI : Fintype (↥F₂ ≃ₐ[ℚ] ↥F₂) := Fintype.ofFinite _
  haveI : Finite (GroupCohomology.RepImage.seq (LF S F₁)).X₃ := finite_repCokernel_LF S F₁
  haveI : Finite (GroupCohomology.RepImage.seq (LF S F₂)).X₃ := finite_repCokernel_LF S F₂
  exact hPITker_gen ((levelMapR F₁ K hle_c.out).comp (levelMapR K F₂ hle_d.out)) B p hB (hTcl S F₁) (hTcl S F₂)
    ((Rep.resFunctor (levelMapR K F₂ hle_d.out)).map (jY S F₁ K Jc hJF_c hJeq_c hJout_c hJunit_c hJinf_c) ≫
      jY S K F₂ Jd hJF_d hJeq_d hJout_d hJunit_d hJinf_d)
    ((Rep.resFunctor (levelMapR K F₂ hle_d.out)).map (jC S F₁ K Jc hJF_c hJeq_c hJout_c hJunit_c hJinf_c) ≫
      jC S K F₂ Jd hJF_d hJeq_d hJout_d hJunit_d hJinf_d)
    ((Rep.resFunctor (levelMapR K F₂ hle_d.out)).map (jCl S F₁ K Jc hJF_c hJeq_c hJout_c hJunit_c hJinf_c) ≫
      jCl S K F₂ Jd hJF_d hJeq_d hJout_d hJunit_d hJinf_d)
    (pasteSq' (levelMapR F₁ K hle_c.out) (levelMapR K F₂ hle_d.out)
      (GroupCohomology.RepImage.ι (LF S F₁)) (GroupCohomology.RepImage.ι (LF S K)) (GroupCohomology.RepImage.ι (LF S F₂))
      (jY S F₁ K Jc hJF_c hJeq_c hJout_c hJunit_c hJinf_c) (jC S F₁ K Jc hJF_c hJeq_c hJout_c hJunit_c hJinf_c)
      (jY S K F₂ Jd hJF_d hJeq_d hJout_d hJunit_d hJinf_d) (jC S K F₂ Jd hJF_d hJeq_d hJout_d hJunit_d hJinf_d)
      (hsqCι S F₁ K Jc hJF_c hJeq_c hJout_c hJunit_c hJinf_c) (hsqCι S K F₂ Jd hJF_d hJeq_d hJout_d hJunit_d hJinf_d))
    (pasteSq' (levelMapR F₁ K hle_c.out) (levelMapR K F₂ hle_d.out)
      (GroupCohomology.RepImage.seq (LF S F₁)).g (GroupCohomology.RepImage.seq (LF S K)).g (GroupCohomology.RepImage.seq (LF S F₂)).g
      (jC S F₁ K Jc hJF_c hJeq_c hJout_c hJunit_c hJinf_c) (jCl S F₁ K Jc hJF_c hJeq_c hJout_c hJunit_c hJinf_c)
      (jC S K F₂ Jd hJF_d hJeq_d hJout_d hJunit_d hJinf_d) (jCl S K F₂ Jd hJF_d hJeq_d hJout_d hJunit_d hJinf_d)
      (hsqCl S F₁ K Jc hJF_c hJeq_c hJout_c hJunit_c hJinf_c) (hsqCl S K F₂ Jd hJF_d hJeq_d hJout_d hJunit_d hJinf_d))
    (hpit_comp_of_right (levelMapR F₁ K hle_c.out) (levelMapR K F₂ hle_d.out) p
      (jCl S F₁ K Jc hJF_c hJeq_c hJout_c hJunit_c hJinf_c) (jCl S K F₂ Jd hJF_d hJeq_d hJout_d hJunit_d hJinf_d)
      (hpit_of_cap S K F₂ Jd hJF_d hJeq_d hJout_d hJunit_d hJinf_d p
        (hcap_of_capClause S K F₂ Jd hJF_d hJeq_d hJout_d hJunit_d hJinf_d hJcont_d hJloc_d hCAP_d)))
    (Infl.inflHom ((levelMapR F₁ K hle_c.out).comp (levelMapR K F₂ hle_d.out)) B
      ((Rep.resFunctor (levelMapR K F₂ hle_d.out)).map (jY S F₁ K Jc hJF_c hJeq_c hJout_c hJunit_c hJinf_c) ≫
        jY S K F₂ Jd hJF_d hJeq_d hJout_d hJunit_d hJinf_d))
    (fun _ => rfl) t χ h

end pitComp
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95 P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95.Infl"

end Reduce95
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95 P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95.Infl"

set_option autoImplicit false
open CategoryTheory groupCohomology NumberField IsDedekindDomain ExtCitation

namespace Reduce95
namespace KD

variable {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
  (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) [FiniteDimensional (ZMod p) M]
  (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p)
  (F₁ : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F₁] [IsGalois ℚ ↥F₁]
  (hF₁S : F₁.IsUnramifiedOutside S)
  (hFM₁ : ∀ s ∈ F₁.fixingSubgroup, ∀ m : M, M.ρ s m = m)
  (B₁ : Rep ℤ (↥F₁ ≃ₐ[ℚ] ↥F₁)) [Fintype B₁] (β : B₁ →+ M.dualTwist (cycloChar p))
  (hβeq₁ : ∀ (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (b : B₁),
    β (B₁.ρ (AlgEquiv.restrictNormalHom ↥F₁ γ) b) = (M.dualTwist (cycloChar p)).ρ γ (β b))
  (hβ : Function.Bijective β) (hB : ∀ b : B₁, p • b = 0)
  (hμ₁ : ∀ u : (AlgebraicClosure ℚ)ˣ, u ^ p = 1 → ∃ e : NumberField.SUnits.sUnitsRep ℚ ↥F₁ (Sq S), iotaE F₁ (Sq S) e = Additive.ofMul u)

def KDClause (K : IntermediateField ℚ (AlgebraicClosure ℚ)) : Prop :=
      ∀ (F₃ : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F₃] [IsGalois ℚ ↥F₃] (_ : K ≤ F₃)
        (π : (↥F₃ ≃ₐ[ℚ] ↥F₃) →* (↥F₁ ≃ₐ[ℚ] ↥F₁))
        (_ : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, π (AlgEquiv.restrictNormalHom ↥F₃ σ) = AlgEquiv.restrictNormalHom ↥F₁ σ)
        (ιE₃ : NumberField.SUnits.sUnitsRep ℚ ↥F₃ (Sq S) →+ Additive (AlgebraicClosure ℚ)ˣ)
        (_ : ∀ x, Additive.toMul (ιE₃ x) = Units.map (algebraMap ↥F₃ (AlgebraicClosure ℚ) : ↥F₃ →* AlgebraicClosure ℚ) (NumberField.SUnits.val ℚ ↥F₃ (Sq S) x))
        (jE : Rep.res π (NumberField.SUnits.sUnitsRep ℚ ↥F₁ (Sq S)) ⟶ NumberField.SUnits.sUnitsRep ℚ ↥F₃ (Sq S))
        (_ : ∀ x, ιE₃ (jE.hom x) = iotaE F₁ (Sq S) x)
        (x : H1 ((ihom (Rep.relationModuleInt B₁)).obj (NumberField.SUnits.sUnitsRep ℚ ↥F₁ (Sq S))))
        (_ : LE2' S hpS M ζ hζ F₁ hF₁S B₁ β hβeq₁ hβ hB x = 0),
        (groupCohomology.map π (Rep.extInflR π B₁ (NumberField.SUnits.sUnitsRep ℚ ↥F₁ (Sq S)) (NumberField.SUnits.sUnitsRep ℚ ↥F₃ (Sq S)) jE) 1).hom x = 0

theorem KDClause.mono {K K' : IntermediateField ℚ (AlgebraicClosure ℚ)} (hKK' : K ≤ K')
    (h : KDClause S hpS M ζ hζ F₁ hF₁S B₁ β hβeq₁ hβ hB K) : KDClause S hpS M ζ hζ F₁ hF₁S B₁ β hβeq₁ hβ hB K' :=
  fun F₃ _ _ hle => h F₃ (hKK'.trans hle)

include hpS hFM₁ hβeq₁ hβ hB hμ₁ in

theorem kd_exists :
    ∃ F₂ : IntermediateField ℚ (AlgebraicClosure ℚ), F₁ ≤ F₂ ∧ FiniteDimensional ℚ ↥F₂ ∧ IsGalois ℚ ↥F₂ ∧ F₂.IsUnramifiedOutside S ∧
      ∀ (F₃ : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F₃] [IsGalois ℚ ↥F₃] (_ : F₂ ≤ F₃)
        (π : (↥F₃ ≃ₐ[ℚ] ↥F₃) →* (↥F₁ ≃ₐ[ℚ] ↥F₁))
        (_ : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, π (AlgEquiv.restrictNormalHom ↥F₃ σ) = AlgEquiv.restrictNormalHom ↥F₁ σ)
        (ιE₃ : NumberField.SUnits.sUnitsRep ℚ ↥F₃ (Sq S) →+ Additive (AlgebraicClosure ℚ)ˣ)
        (_ : ∀ x, Additive.toMul (ιE₃ x) = Units.map (algebraMap ↥F₃ (AlgebraicClosure ℚ) : ↥F₃ →* AlgebraicClosure ℚ) (NumberField.SUnits.val ℚ ↥F₃ (Sq S) x))
        (jE : Rep.res π (NumberField.SUnits.sUnitsRep ℚ ↥F₁ (Sq S)) ⟶ NumberField.SUnits.sUnitsRep ℚ ↥F₃ (Sq S))
        (_ : ∀ x, ιE₃ (jE.hom x) = iotaE F₁ (Sq S) x)
        (x : H1 ((ihom (Rep.relationModuleInt B₁)).obj (NumberField.SUnits.sUnitsRep ℚ ↥F₁ (Sq S))))
        (_ : LE2' S hpS M ζ hζ F₁ hF₁S B₁ β hβeq₁ hβ hB x = 0),
        (groupCohomology.map π (Rep.extInflR π B₁ (NumberField.SUnits.sUnitsRep ℚ ↥F₁ (Sq S)) (NumberField.SUnits.sUnitsRep ℚ ↥F₃ (Sq S)) jE) 1).hom x = 0 :=
  NumberField.SUnits.exists_level_forall_map_extInflR_eq_zero_of_isGlobalBridge2_apply_eq_zero S hpS (Sq S) (coe_Sq S) M F₁ hF₁S hFM₁ B₁ hB
    (iotaE F₁ (Sq S)) (toMul_iotaE F₁ (Sq S)) hμ₁ (kappa M ζ hζ B₁ β)
    (kappa_equivariant M ζ hζ (AlgEquiv.restrictNormalHom ↥F₁) B₁ β hβeq₁) (kappa_perfect M ζ hζ B₁ β hβ hB)
    (LE2'_spec S hpS M ζ hζ F₁ hF₁S B₁ β hβeq₁ hβ hB)

noncomputable def kdLevel : IntermediateField ℚ (AlgebraicClosure ℚ) :=
  (kd_exists S hpS M ζ hζ F₁ hF₁S hFM₁ B₁ β hβeq₁ hβ hB hμ₁).choose

include hpS hFM₁ hβeq₁ hβ hB hμ₁ in
theorem le_kdLevel : F₁ ≤ kdLevel S hpS M ζ hζ F₁ hF₁S hFM₁ B₁ β hβeq₁ hβ hB hμ₁ :=
  (kd_exists S hpS M ζ hζ F₁ hF₁S hFM₁ B₁ β hβeq₁ hβ hB hμ₁).choose_spec.1

include hpS hFM₁ hβeq₁ hβ hB hμ₁ in
theorem finiteDimensional_kdLevel : FiniteDimensional ℚ ↥(kdLevel S hpS M ζ hζ F₁ hF₁S hFM₁ B₁ β hβeq₁ hβ hB hμ₁) :=
  (kd_exists S hpS M ζ hζ F₁ hF₁S hFM₁ B₁ β hβeq₁ hβ hB hμ₁).choose_spec.2.1

include hpS hFM₁ hβeq₁ hβ hB hμ₁ in
theorem isGalois_kdLevel : IsGalois ℚ ↥(kdLevel S hpS M ζ hζ F₁ hF₁S hFM₁ B₁ β hβeq₁ hβ hB hμ₁) :=
  (kd_exists S hpS M ζ hζ F₁ hF₁S hFM₁ B₁ β hβeq₁ hβ hB hμ₁).choose_spec.2.2.1

include hpS hFM₁ hβeq₁ hβ hB hμ₁ in
theorem isUnramifiedOutside_kdLevel : (kdLevel S hpS M ζ hζ F₁ hF₁S hFM₁ B₁ β hβeq₁ hβ hB hμ₁).IsUnramifiedOutside S :=
  (kd_exists S hpS M ζ hζ F₁ hF₁S hFM₁ B₁ β hβeq₁ hβ hB hμ₁).choose_spec.2.2.2.1

include hpS hFM₁ hβeq₁ hβ hB hμ₁ in

theorem kdClause_kdLevel : KDClause S hpS M ζ hζ F₁ hF₁S B₁ β hβeq₁ hβ hB (kdLevel S hpS M ζ hζ F₁ hF₁S hFM₁ B₁ β hβeq₁ hβ hB hμ₁) :=
  (kd_exists S hpS M ζ hζ F₁ hF₁S hFM₁ B₁ β hβeq₁ hβ hB hμ₁).choose_spec.2.2.2.2

open Reduce95.Infl in

theorem hB3ker_of_KDClause {K : IntermediateField ℚ (AlgebraicClosure ℚ)} (hK : KDClause S hpS M ζ hζ F₁ hF₁S B₁ β hβeq₁ hβ hB K)
    (F₂ : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F₂] [IsGalois ℚ ↥F₂] (hle : K ≤ F₂)
    (π₁₂ : (↥F₂ ≃ₐ[ℚ] ↥F₂) →* (↥F₁ ≃ₐ[ℚ] ↥F₁))
    (hπ₁₂ : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, π₁₂ (AlgEquiv.restrictNormalHom ↥F₂ σ) = AlgEquiv.restrictNormalHom ↥F₁ σ)
    (jE₂ : Rep.res π₁₂ (seqF S F₁).X₁ ⟶ (seqF S F₂).X₁)
    (hjE₂ : ∀ x, iotaE F₂ (Sq S) (jE₂.hom x) = iotaE F₁ (Sq S) x) :
    ∀ x : H1 ((ihom (Rep.relationModuleInt B₁)).obj (seqF S F₁).X₁),
      LE2' S hpS M ζ hζ F₁ hF₁S B₁ β hβeq₁ hβ hB x = 0 → inflExt1 π₁₂ B₁ jE₂ x = 0 := by
  intro x hx
  rw [inflExt1_apply]
  exact hK F₂ hle π₁₂ hπ₁₂ (iotaE F₂ (Sq S)) (toMul_iotaE F₂ (Sq S)) jE₂ hjE₂ x hx

open Reduce95.Infl in
include hFM₁ hμ₁ in

theorem hB3ker (F₂ : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F₂] [IsGalois ℚ ↥F₂]
    (hle : kdLevel S hpS M ζ hζ F₁ hF₁S hFM₁ B₁ β hβeq₁ hβ hB hμ₁ ≤ F₂)
    (π₁₂ : (↥F₂ ≃ₐ[ℚ] ↥F₂) →* (↥F₁ ≃ₐ[ℚ] ↥F₁))
    (hπ₁₂ : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, π₁₂ (AlgEquiv.restrictNormalHom ↥F₂ σ) = AlgEquiv.restrictNormalHom ↥F₁ σ)
    (jE₂ : Rep.res π₁₂ (seqF S F₁).X₁ ⟶ (seqF S F₂).X₁)
    (hjE₂ : ∀ x, iotaE F₂ (Sq S) (jE₂.hom x) = iotaE F₁ (Sq S) x) :
    ∀ x : H1 ((ihom (Rep.relationModuleInt B₁)).obj (seqF S F₁).X₁),
      LE2' S hpS M ζ hζ F₁ hF₁S B₁ β hβeq₁ hβ hB x = 0 → inflExt1 π₁₂ B₁ jE₂ x = 0 := by
  intro x hx
  rw [inflExt1_apply]
  exact (kd_exists S hpS M ζ hζ F₁ hF₁S hFM₁ B₁ β hβeq₁ hβ hB hμ₁).choose_spec.2.2.2.2 F₂ hle π₁₂ hπ₁₂
    (iotaE F₂ (Sq S)) (toMul_iotaE F₂ (Sq S)) jE₂ hjE₂ x hx

end Reduce95.KD
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95 P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95.Infl"
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95 P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95.Infl"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxSynthPendingDepth 3
open CategoryTheory IsDedekindDomain NumberField

namespace Reduce95
open ExtCitation groupCohomology GroupCohomology M4aHerbrand
open scoped NumberField.PlaceDecomp

section kdclause

variable {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes)

def KDClauseOf (Sℚ : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (F₁ : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F₁] [IsGalois ℚ ↥F₁]
    (B : Rep ℤ (↥F₁ ≃ₐ[ℚ] ↥F₁))
    (ιE₁ : NumberField.SUnits.sUnitsRep ℚ ↥F₁ Sℚ →+ Additive (AlgebraicClosure ℚ)ˣ)
    (Λ₁ : H1 ((ihom (Rep.relationModuleInt B)).obj (NumberField.SUnits.sUnitsRep ℚ ↥F₁ Sℚ)) →+ continuousH2S S M)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) : Prop :=
  ∀ (F₃ : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F₃] [IsGalois ℚ ↥F₃] (_ : K ≤ F₃)
    (π : (↥F₃ ≃ₐ[ℚ] ↥F₃) →* (↥F₁ ≃ₐ[ℚ] ↥F₁))
    (_ : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, π (AlgEquiv.restrictNormalHom ↥F₃ σ) = AlgEquiv.restrictNormalHom ↥F₁ σ)
    (ιE₃ : NumberField.SUnits.sUnitsRep ℚ ↥F₃ Sℚ →+ Additive (AlgebraicClosure ℚ)ˣ)
    (_ : ∀ x, Additive.toMul (ιE₃ x) = Units.map (algebraMap ↥F₃ (AlgebraicClosure ℚ) : ↥F₃ →* AlgebraicClosure ℚ) (NumberField.SUnits.val ℚ ↥F₃ Sℚ x))
    (jE : Rep.res π (NumberField.SUnits.sUnitsRep ℚ ↥F₁ Sℚ) ⟶ NumberField.SUnits.sUnitsRep ℚ ↥F₃ Sℚ)
    (_ : ∀ x, ιE₃ (jE.hom x) = ιE₁ x)
    (x : H1 ((ihom (Rep.relationModuleInt B)).obj (NumberField.SUnits.sUnitsRep ℚ ↥F₁ Sℚ))) (_ : Λ₁ x = 0),
    (groupCohomology.map π (Rep.extInflR π B (NumberField.SUnits.sUnitsRep ℚ ↥F₁ Sℚ) (NumberField.SUnits.sUnitsRep ℚ ↥F₃ Sℚ) jE) 1).hom x = 0

theorem KDClauseOf.mono {Sℚ : Finset (HeightOneSpectrum (𝓞 ℚ))} {M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)}
    {F₁ : IntermediateField ℚ (AlgebraicClosure ℚ)} [NumberField ↥F₁] [IsGalois ℚ ↥F₁] {B : Rep ℤ (↥F₁ ≃ₐ[ℚ] ↥F₁)}
    {ιE₁ : NumberField.SUnits.sUnitsRep ℚ ↥F₁ Sℚ →+ Additive (AlgebraicClosure ℚ)ˣ}
    {Λ₁ : H1 ((ihom (Rep.relationModuleInt B)).obj (NumberField.SUnits.sUnitsRep ℚ ↥F₁ Sℚ)) →+ continuousH2S S M}
    {K K' : IntermediateField ℚ (AlgebraicClosure ℚ)} (hKK' : K ≤ K') (h : KDClauseOf S Sℚ M F₁ B ιE₁ Λ₁ K) :
    KDClauseOf S Sℚ M F₁ B ιE₁ Λ₁ K' :=
  fun F₃ _ _ hle π hπ ιE₃ hιE₃ jE hjE x hx => h F₃ (hKK'.trans hle) π hπ ιE₃ hιE₃ jE hjE x hx

end kdclause
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95 P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95.Infl"

section lower

variable {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
  (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) [FiniteDimensional (ZMod p) M]
  (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F] (hFS : F.IsUnramifiedOutside S)

include hpS hFS in

theorem exists_lower_levels :
    ∃ (Fc F₁ : IntermediateField ℚ (AlgebraicClosure ℚ))
      (_ : NumberField ↥Fc) (_ : IsGalois ℚ ↥Fc) (_ : NumberField ↥F₁) (_ : IsGalois ℚ ↥F₁)
      (h0c : F ≤ Fc) (_ : Fc ≤ F₁),
      Fc.IsUnramifiedOutside S ∧ F₁.IsUnramifiedOutside S ∧
      CapClause (p := p) S F Fc ∧ SepClause S Fc F₁ (Bofπ F M (levelMapR F Fc h0c)) := by
  obtain ⟨Fc, h0c, instNFc, hFcS, instGc, hcap⟩ :=
    NumberField.exists_le_isGalois_forall_mem_range_sup_unitIdelesOutside_of_pow_mem S hpS F hFS
  haveI := instGc
  obtain ⟨F₁, hc1, instNF₁, instG₁, hF₁S, hsep⟩ :=
    M4aHerbrand.exists_level_forall_relationHom_sIdeleClassGroup_extends_or_map_delta_ne_zero S hpS Fc hFcS
      (DD Fc) (DD_stab S Fc) (fun _ _ => rfl) (Bofπ F M (levelMapR F Fc h0c)) (Bofπ_torsion F M (levelMapR F Fc h0c))
  exact ⟨Fc, F₁, instNFc, instGc, instNF₁, instG₁, h0c, hc1, hFcS, hF₁S, fun _ => hcap,
    fun π hπ D' hD' _ hact' j hX φ => hsep π hπ D' hD' hact' j hX φ⟩

end lower
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95 P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95.Infl"

section upper

variable {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
  (Sℚ : Finset (HeightOneSpectrum (𝓞 ℚ))) (hSℚ : (↑Sℚ : Set (HeightOneSpectrum (𝓞 ℚ))) = NumberField.placesOverPrimes ℚ (↑S : Set Nat.Primes))
  (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
  (F₁ : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F₁] [IsGalois ℚ ↥F₁] (hF₁ : F₁.IsUnramifiedOutside S)
  (hFM : ∀ s ∈ F₁.fixingSubgroup, ∀ m : M, M.ρ s m = m)
  (B : Rep ℤ (↥F₁ ≃ₐ[ℚ] ↥F₁)) [Fintype B] (hB : ∀ b : B, p • b = 0)
  (ιE₁ : NumberField.SUnits.sUnitsRep ℚ ↥F₁ Sℚ →+ Additive (AlgebraicClosure ℚ)ˣ)
  (hιE₁ : ∀ x, Additive.toMul (ιE₁ x) = Units.map (algebraMap ↥F₁ (AlgebraicClosure ℚ) : ↥F₁ →* AlgebraicClosure ℚ) (NumberField.SUnits.val ℚ ↥F₁ Sℚ x))
  (hμ : ∀ u : (AlgebraicClosure ℚ)ˣ, u ^ p = 1 → ∃ e : NumberField.SUnits.sUnitsRep ℚ ↥F₁ Sℚ, ιE₁ e = Additive.ofMul u)
  (κ : B →+ M →+ Additive (AlgebraicClosure ℚ)ˣ)
  (hκeq : ∀ (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (b : B) (m : M),
    κ (B.ρ (AlgEquiv.restrictNormalHom ↥F₁ γ) b) (M.ρ γ m) = (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)).ρ γ (κ b m))
  (hκ : ∀ c : B →+ Additive (AlgebraicClosure ℚ)ˣ, ∃! m : M, ∀ b, κ b m = c b)
  {Λ₁ : H1 ((ihom (Rep.relationModuleInt B)).obj (NumberField.SUnits.sUnitsRep ℚ ↥F₁ Sℚ)) →+ continuousH2S S M}
  (hΛ₁ : IsGlobalBridge₂ S (AlgEquiv.restrictNormalHom ↥F₁) (Rep.relationModuleInt.ι B) (Rep.freeCover B)
    (A := Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)) ιE₁ κ Λ₁)

include hpS hSℚ hF₁ hFM hB hιE₁ hμ hκeq hκ hΛ₁ in

theorem exists_upper_levels_of_isGlobalBridge2 :
    ∃ (K F₂ : IntermediateField ℚ (AlgebraicClosure ℚ))
      (_ : NumberField ↥K) (_ : IsGalois ℚ ↥K) (_ : NumberField ↥F₂) (_ : IsGalois ℚ ↥F₂)
      (_ : F₁ ≤ K) (_ : K ≤ F₂),
      K.IsUnramifiedOutside S ∧ F₂.IsUnramifiedOutside S ∧
      KDClauseOf S Sℚ M F₁ B ιE₁ Λ₁ K ∧ CapClause (p := p) S K F₂ := by
  obtain ⟨K, h1K, fdK, galK, hKS, hkd⟩ :=
    NumberField.SUnits.exists_level_forall_map_extInflR_eq_zero_of_isGlobalBridge2_apply_eq_zero S hpS Sℚ hSℚ M F₁ hF₁ hFM B hB
      ιE₁ hιE₁ hμ κ hκeq hκ hΛ₁
  haveI := fdK
  haveI := galK
  haveI : NumberField ↥K := ⟨⟩
  obtain ⟨F₂, hK2, instNF₂, hF₂S, instG₂, hcap⟩ :=
    NumberField.exists_le_isGalois_forall_mem_range_sup_unitIdelesOutside_of_pow_mem S hpS K hKS
  exact ⟨K, F₂, inferInstance, galK, instNF₂, instG₂, h1K, hK2, hKS, hF₂S,
    fun F₃ _ _ hle π hπ ιE₃ hιE₃ jE hjE x hx => hkd F₃ hle π hπ ιE₃ hιE₃ jE hjE x hx, fun _ => hcap⟩

end upper
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95 P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95.Infl"

section upperKD

variable {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
  (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) [FiniteDimensional (ZMod p) M]
  (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p)
  (F₁ : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F₁] [IsGalois ℚ ↥F₁]
  (hF₁S : F₁.IsUnramifiedOutside S)
  (hFM₁ : ∀ s ∈ F₁.fixingSubgroup, ∀ m : M, M.ρ s m = m)
  (B₁ : Rep ℤ (↥F₁ ≃ₐ[ℚ] ↥F₁)) [Fintype B₁] (β : B₁ →+ M.dualTwist (cycloChar p))
  (hβeq₁ : ∀ (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (b : B₁),
    β (B₁.ρ (AlgEquiv.restrictNormalHom ↥F₁ γ) b) = (M.dualTwist (cycloChar p)).ρ γ (β b))
  (hβ : Function.Bijective β) (hB : ∀ b : B₁, p • b = 0)
  (hμ₁ : ∀ u : (AlgebraicClosure ℚ)ˣ, u ^ p = 1 → ∃ e : NumberField.SUnits.sUnitsRep ℚ ↥F₁ (Sq S), iotaE F₁ (Sq S) e = Additive.ofMul u)

include hFM₁ hμ₁ in

theorem exists_upper_levels :
    ∃ (K F₂ : IntermediateField ℚ (AlgebraicClosure ℚ))
      (_ : NumberField ↥K) (_ : IsGalois ℚ ↥K) (_ : NumberField ↥F₂) (_ : IsGalois ℚ ↥F₂)
      (_ : F₁ ≤ K) (_ : K ≤ F₂),
      K.IsUnramifiedOutside S ∧ F₂.IsUnramifiedOutside S ∧
      Reduce95.KD.KDClause S hpS M ζ hζ F₁ hF₁S B₁ β hβeq₁ hβ hB K ∧ CapClause (p := p) S K F₂ := by
  haveI := Reduce95.KD.finiteDimensional_kdLevel S hpS M ζ hζ F₁ hF₁S hFM₁ B₁ β hβeq₁ hβ hB hμ₁
  haveI := Reduce95.KD.isGalois_kdLevel S hpS M ζ hζ F₁ hF₁S hFM₁ B₁ β hβeq₁ hβ hB hμ₁
  haveI : NumberField ↥(Reduce95.KD.kdLevel S hpS M ζ hζ F₁ hF₁S hFM₁ B₁ β hβeq₁ hβ hB hμ₁) := ⟨⟩
  have hKS := Reduce95.KD.isUnramifiedOutside_kdLevel S hpS M ζ hζ F₁ hF₁S hFM₁ B₁ β hβeq₁ hβ hB hμ₁
  obtain ⟨F₂, hK2, instNF₂, hF₂S, instG₂, hcap⟩ :=
    NumberField.exists_le_isGalois_forall_mem_range_sup_unitIdelesOutside_of_pow_mem S hpS
      (Reduce95.KD.kdLevel S hpS M ζ hζ F₁ hF₁S hFM₁ B₁ β hβeq₁ hβ hB hμ₁) hKS
  exact ⟨_, F₂, inferInstance, inferInstance, instNF₂, instG₂,
    Reduce95.KD.le_kdLevel S hpS M ζ hζ F₁ hF₁S hFM₁ B₁ β hβeq₁ hβ hB hμ₁, hK2, hKS, hF₂S,
    Reduce95.KD.kdClause_kdLevel S hpS M ζ hζ F₁ hF₁S hFM₁ B₁ β hβeq₁ hβ hB hμ₁, fun _ => hcap⟩

end upperKD
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95 P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95.Infl"

end Reduce95
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95 P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95.Infl"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
open CategoryTheory groupCohomology NumberField IsDedekindDomain ExtCitation

namespace Reduce95

section generic

variable {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))

def ConstMod (F : IntermediateField ℚ (AlgebraicClosure ℚ)) {X : Type}
    (m : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → X) : Prop :=
  ∀ (g g' s s' : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), s ∈ F.fixingSubgroup → s' ∈ F.fixingSubgroup →
    m (g * s, g' * s') = m (g, g')

theorem ConstMod.mono {F F' : IntermediateField ℚ (AlgebraicClosure ℚ)} (h : F ≤ F') {X : Type}
    {m : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → X} (hm : ConstMod F m) :
    ConstMod F' m :=
  fun g g' s s' hs hs' => hm g g' s s' (IntermediateField.fixingSubgroup_antitone h hs) (IntermediateField.fixingSubgroup_antitone h hs')

def RepConst (F : IntermediateField ℚ (AlgebraicClosure ℚ)) (c : continuousH2S S M) : Prop :=
  ∃ (m : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → M)
    (hm : m ∈ levelCocyclesS₂ S M), continuousH2Sπ S M ⟨m, hm⟩ = c ∧ ConstMod F m

theorem RepConst.mono {F F' : IntermediateField ℚ (AlgebraicClosure ℚ)} (h : F ≤ F') {c : continuousH2S S M}
    (hc : RepConst S M F c) : RepConst S M F' c := by
  obtain ⟨m, hm, hmc, hconst⟩ := hc
  exact ⟨m, hm, hmc, hconst.mono h⟩

theorem RepConst.zero (F : IntermediateField ℚ (AlgebraicClosure ℚ)) : RepConst S M F 0 :=
  ⟨0, Submodule.zero_mem _, by rw [← map_zero (continuousH2Sπ S M)]; rfl, fun _ _ _ _ _ _ => rfl⟩

theorem RepConst.add {F : IntermediateField ℚ (AlgebraicClosure ℚ)} {c c' : continuousH2S S M}
    (hc : RepConst S M F c) (hc' : RepConst S M F c') : RepConst S M F (c + c') := by
  obtain ⟨m, hm, rfl, hconst⟩ := hc
  obtain ⟨m', hm', rfl, hconst'⟩ := hc'
  refine ⟨m + m', Submodule.add_mem _ hm hm', (map_add (continuousH2Sπ S M) ⟨m, hm⟩ ⟨m', hm'⟩).symm ▸ rfl, ?_⟩
  intro g g' s s' hs hs'
  change m (g * s, g' * s') + m' (g * s, g' * s') = m (g, g') + m' (g, g')
  rw [hconst g g' s s' hs hs', hconst' g g' s s' hs hs']

theorem RepConst.smul {F : IntermediateField ℚ (AlgebraicClosure ℚ)} (a : ZMod p) {c : continuousH2S S M}
    (hc : RepConst S M F c) : RepConst S M F (a • c) := by
  obtain ⟨m, hm, rfl, hconst⟩ := hc
  refine ⟨a • m, Submodule.smul_mem _ a hm, (map_smul (continuousH2Sπ S M) a ⟨m, hm⟩).symm ▸ rfl, ?_⟩
  intro g g' s s' hs hs'
  change a • m (g * s, g' * s') = a • m (g, g')
  rw [hconst g g' s s' hs hs']

theorem exists_level_constMod (m : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → M)
    (hm : m ∈ levelCocyclesS₂ S M) :
    ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧ ConstMod F m := by
  obtain ⟨F, hFS, hF⟩ := ((mem_levelCocyclesS₂_iff S M m).1 hm).2
  exact ⟨F, hFS, hF⟩

theorem exists_shaConstLevel [Module.Finite (ZMod p) (continuousH2S S M)] :
    ∃ Fx : IntermediateField ℚ (AlgebraicClosure ℚ), Fx.IsUnramifiedOutside S ∧ ∀ c : continuousH2S S M, RepConst S M Fx c := by
  classical
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := ZMod p) (M := continuousH2S S M)

  have hrep : ∀ i : Fin n, ∃ (F : IntermediateField ℚ (AlgebraicClosure ℚ)), F.IsUnramifiedOutside S ∧ RepConst S M F (s i) := by
    intro i
    obtain ⟨⟨m, hm⟩, hmc⟩ := Submodule.mkQ_surjective _ (s i)
    obtain ⟨F, hFS, hF⟩ := exists_level_constMod S M m hm
    exact ⟨F, hFS, m, hm, hmc, hF⟩
  choose Fi hFiS hFi using hrep
  refine ⟨Finset.univ.sup Fi, ?_, ?_⟩
  · exact Finset.sup_induction (p := fun F : IntermediateField ℚ (AlgebraicClosure ℚ) => F.IsUnramifiedOutside S)
      (IntermediateField.isUnramifiedOutside_bot S)
      (fun _ ha _ hb => IntermediateField.IsUnramifiedOutside.sup ha hb) (fun i _ => hFiS i)
  · intro c
    have hc : c ∈ Submodule.span (ZMod p) (Set.range s) := by rw [hs]; exact Submodule.mem_top
    induction hc using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact (hFi i).mono S M (Finset.le_sup (Finset.mem_univ i))
    | zero => exact RepConst.zero S M _
    | add x y _ _ hx hy => exact hx.add S M hy
    | smul a x _ hx => exact hx.smul S M a

end generic
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95 P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95.Infl"

section realise

theorem hSTAB_of_level
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (Sℚ : Finset (HeightOneSpectrum (𝓞 ℚ))) (hSℚ : (↑Sℚ : Set (HeightOneSpectrum (𝓞 ℚ))) = NumberField.placesOverPrimes ℚ (↑S : Set Nat.Primes))
    (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F] (hF : F.IsUnramifiedOutside S)
    (hζF : ζ ∈ F) (hFM : ∀ s ∈ F.fixingSubgroup, ∀ x : M, M.ρ s x = x)
    (B : Rep ℤ (↥F ≃ₐ[ℚ] ↥F)) [Fintype B] (hB : ∀ b : B, p • b = 0)
    (ιE : (NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ) →+ Additive (AlgebraicClosure ℚ)ˣ)
    (hιE : ∀ x, Additive.toMul (ιE x) = Units.map (algebraMap ↥F (AlgebraicClosure ℚ) : ↥F →* AlgebraicClosure ℚ) (NumberField.SUnits.val ℚ ↥F Sℚ x))
    (κ : B →+ M →+ Additive (AlgebraicClosure ℚ)ˣ)
    (hκeq : ∀ (γ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (b : B) (x : M),
      κ (B.ρ (AlgEquiv.restrictNormalHom ↥F γ) b) (M.ρ γ x) = (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)).ρ γ (κ b x))
    (hκ : ∀ c : B →+ Additive (AlgebraicClosure ℚ)ˣ, ∃! x : M, ∀ b, κ b x = c b)
    {ΛE : H1 ((ihom (Rep.relationModuleInt B)).obj (NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ)) →+ continuousH2S S M}
    (hΛE : IsGlobalBridge₂ S (AlgEquiv.restrictNormalHom ↥F) (Rep.relationModuleInt.ι B) (Rep.freeCover B)
      (A := Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)) ιE κ ΛE)

    (Fx : IntermediateField ℚ (AlgebraicClosure ℚ)) (hreps : ∀ c : continuousH2S S M, RepConst S M Fx c) (hle : Fx ≤ F) :
    ∀ c : continuousH2S S M, c ∈ sha₂ S M → ∃ x, ΛE x = c := by
  intro c _
  obtain ⟨m, hm, hmc, hconst⟩ := (hreps c).mono S M hle
  obtain ⟨x, hx⟩ := NumberField.SUnits.exists_isGlobalBridge2_apply_eq_continuousH2Spi_of_forall_mul_eq S hpS Sℚ hSℚ M ζ hζ F hF hζF hFM
    B hB ιE hιE κ hκeq hκ hΛE m hm hconst
  exact ⟨x, hx.trans hmc⟩

end realise
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95 P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95.Infl"

section dock

variable {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
  (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) [FiniteDimensional (ZMod p) M]
  (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p)
  (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F]
  (hFS : F.IsUnramifiedOutside S) (hζF : ζ ∈ F) (hFM : ∀ s ∈ F.fixingSubgroup, ∀ x : M, M.ρ s x = x)
  (B : Rep ℤ (↥F ≃ₐ[ℚ] ↥F)) [Fintype B] (β : B →+ M.dualTwist (cycloChar p))
  (hβeq : ∀ (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (b : B),
    β (B.ρ (AlgEquiv.restrictNormalHom ↥F γ) b) = (M.dualTwist (cycloChar p)).ρ γ (β b))
  (hβ : Function.Bijective β) (hB : ∀ b : B, p • b = 0)

include hζF hFM in

theorem hSTAB_dock (Fx : IntermediateField ℚ (AlgebraicClosure ℚ)) (hreps : ∀ c : continuousH2S S M, RepConst S M Fx c) (hle : Fx ≤ F) :
    ∀ c : continuousH2S S M, c ∈ sha₂ S M → ∃ x, LE2' S hpS M ζ hζ F hFS B β hβeq hβ hB x = c :=
  hSTAB_of_level S hpS (Sq S) (coe_Sq S) M ζ hζ F hFS hζF hFM B hB (iotaE F (Sq S)) (toMul_iotaE F (Sq S))
    (kappa M ζ hζ B β) (kappa_equivariant M ζ hζ (AlgEquiv.restrictNormalHom ↥F) B β hβeq) (kappa_perfect M ζ hζ B β hβ hB)
    (LE2'_spec S hpS M ζ hζ F hFS B β hβeq hβ hB) Fx hreps hle

end dock
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95 P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95.Infl"

end Reduce95
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95 P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95.Infl"

set_option autoImplicit false
set_option maxHeartbeats 12800000
set_option synthInstance.maxHeartbeats 1600000
open CategoryTheory Module groupCohomology ExtCitation NumberField GroupCohomology IsDedekindDomain M4aHerbrand

local instance factPrimesDock (q : Nat.Primes) : Fact ((q : ℕ)).Prime := ⟨q.2⟩

namespace Reduce95

theorem inv_comp₂ {G G₁ G₂ : Type} [Group G] [Group G₁] [Group G₂] (π : G₁ →* G) (π' : G₂ →* G₁)
    {C : Rep ℤ G} {C₁ : Rep ℤ G₁} {C₂ : Rep ℤ G₂} (jC : Rep.res π C ⟶ C₁) (jC' : Rep.res π' C₁ ⟶ C₂)
    {A : Type} (inv : ↥(groupCohomology C 2) → A) (inv₁ : ↥(groupCohomology C₁ 2) → A) (inv₂ : ↥(groupCohomology C₂ 2) → A)
    (h : ∀ c, inv₁ ((groupCohomology.map π jC 2).hom c) = inv c) (h' : ∀ c, inv₂ ((groupCohomology.map π' jC' 2).hom c) = inv₁ c)
    (c : ↥(groupCohomology C 2)) :
    inv₂ ((groupCohomology.map (π.comp π') ((Rep.resFunctor π').map jC ≫ jC' : Rep.res (π.comp π') C ⟶ C₂) 2).hom c) = inv c := by
  have hc := groupCohomology.map_comp π π' jC jC' 2
  have := congrArg (fun φ => (ModuleCat.Hom.hom φ) c) hc
  change (groupCohomology.map (π.comp π') ((Rep.resFunctor π').map jC ≫ jC') 2).hom c =
    (groupCohomology.map π' jC' 2).hom ((groupCohomology.map π jC 2).hom c) at this
  rw [this, h', h]
end Reduce95
p2m_reactivate "P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95 P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95.Infl"

theorem isEquivariantBilinear_eval_res_local' {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (v : extArithIndex S)
    (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) :
    Rep.IsEquivariantBilinear (Rep.res (extArithLoc S v) M : Rep.{0} (ZMod p) (extArithLocalGroups S v))
      (Rep.res (extArithLoc S v) (M.dualTwist (cycloChar p)) : Rep.{0} (ZMod p) (extArithLocalGroups S v))
      (ofChar (k := ZMod p) ((cycloChar p).comp (extArithLoc S v)))
      (Module.Dual.eval (ZMod p) M :
          Rep.res (extArithLoc S v) M →ₗ[ZMod p]
            Rep.res (extArithLoc S v) (M.dualTwist (cycloChar p)) →ₗ[ZMod p]
              ofChar (k := ZMod p) ((cycloChar p).comp (extArithLoc S v))) := by
  intro g a b
  exact Rep.isEquivariantBilinear_eval_dualTwist M (cycloChar p) (extArithLoc S v g) a b

open Reduce95 Reduce95.Infl Reduce95.KD in
theorem solution
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    [FiniteDimensional (ZMod p) M]
    (hsm : ∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s ∈ F.fixingSubgroup, M.ρ s m = m)
    (hMur : ∀ q : Nat.Primes, q ∉ S → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
      A.LiesOverPrime (q : ℕ) → ∀ g ∈ A.inertiaSubgroupIn ℚ, M.ρ g = 1) :
    ∃ B : sha₁ S (M.dualTwist (cycloChar p)) →ₗ[ZMod p] sha₂ S M →ₗ[ZMod p] ZMod p,
      (∀ y, (∀ x, B y x = 0) → y = 0) ∧ (∀ x, (∀ y, B y x = 0) → x = 0) := by
  classical

  haveI hfin : FiniteDimensional (ZMod p) ↥(continuousH1S S (M.dualTwist (cycloChar p))) :=
    groupCohomology.finiteDimensional_continuousH1S S (M.dualTwist (cycloChar p)) (Rep.dualTwist_cycloChar_smooth M hsm)
  have hloc : ∀ y ∈ continuousH1S S (M.dualTwist (cycloChar p)), ∀ v : extArithIndex S,
      locTotal (extArithLoc S) (M.dualTwist (cycloChar p)) y v ∈
        continuousH1 (extArithLoc S v) (Rep.res (extArithLoc S v) (M.dualTwist (cycloChar p))) :=
    fun y hy v => groupCohomology.locRes_mem_continuousH1_of_mem_continuousH1S S (M.dualTwist (cycloChar p)) y hy v

  obtain ⟨ζ, hζ⟩ : ∃ ζ : AlgebraicClosure ℚ, IsPrimitiveRoot ζ p := by
    haveI : NeZero ((p : ℕ) : AlgebraicClosure ℚ) := NeZero.charZero
    exact HasEnoughRootsOfUnity.prim

  have hfinite : ∀ q : ↥S, ∃ θq : continuousH1 (extArithLoc S (Sum.inr q)) (Rep.res (extArithLoc S (Sum.inr q)) M) →ₗ[ZMod p]
      Module.Dual (ZMod p) (continuousH1 (extArithLoc S (Sum.inr q)) (Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p)))),
      (haveI : Fact (((q : Nat.Primes) : ℕ)).Prime := ⟨(q : Nat.Primes).prop⟩
       IsTheta1 (extArithLoc S (Sum.inr q))
        (Module.Dual.eval (ZMod p) M :
          Rep.res (extArithLoc S (Sum.inr q)) M →ₗ[ZMod p]
            Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p)) →ₗ[ZMod p]
              ofChar (k := ZMod p) ((cycloChar p).comp (extArithLoc S (Sum.inr q))))
        (localInv p ζ (q : Nat.Primes)) θq) ∧ Function.Bijective θq := by
    intro q
    haveI : Fact (((q : Nat.Primes) : ℕ)).Prime := ⟨(q : Nat.Primes).prop⟩
    obtain ⟨θ₁, hθ₁⟩ := groupCohomology.exists_theta1
      (M := Rep.res (extArithLoc S (Sum.inr q)) M) (D := Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p)))
      (N := ofChar (k := ZMod p) ((cycloChar p).comp (extArithLoc S (Sum.inr q))))
      (extArithLoc S (Sum.inr q))
      (Module.Dual.eval (ZMod p) M :
        Rep.res (extArithLoc S (Sum.inr q)) M →ₗ[ZMod p]
          Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p)) →ₗ[ZMod p]
            ofChar (k := ZMod p) ((cycloChar p).comp (extArithLoc S (Sum.inr q))))
      (isEquivariantBilinear_eval_res_local' S (Sum.inr q) M)
      (fun x => by
        obtain ⟨F, hF, hFx⟩ := Rep.dualTwist_cycloChar_smooth M hsm (show M.dualTwist (cycloChar p) from x)
        exact ⟨F, hF, fun s hs => hFx _ hs⟩)
      (localInv p ζ (q : Nat.Primes))
    exact ⟨θ₁, hθ₁, groupCohomology.bijective_of_isTheta1_localInv_extArithLoc S q M hsm ζ hζ θ₁ hθ₁⟩
  choose θq hθq1 hθqbij using hfinite

  have hinf : ∀ u : Unit, ∃ θu : continuousH1 (extArithLoc S (Sum.inl u)) (Rep.res (extArithLoc S (Sum.inl u)) M) →ₗ[ZMod p]
      Module.Dual (ZMod p) (continuousH1 (extArithLoc S (Sum.inl u)) (Rep.res (extArithLoc S (Sum.inl u)) (M.dualTwist (cycloChar p)))),
      Function.Bijective θu := by
    intro u

    have hsub : ∀ (A : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) [FiniteDimensional (ZMod p) A],
        Subsingleton (H1 (Rep.res (extArithLoc S (Sum.inl u)) A)) := by
      intro A _
      refine ⟨fun x y => ?_⟩
      have hx : ∀ z : H1 (Rep.res (extArithLoc S (Sum.inl u)) A), z = 0 := by
        intro z
        by_contra hz
        have h1 : Module.finrank (ZMod p) ↥((ZMod p) ∙ z) = 1 := finrank_span_singleton hz
        have h0 := groupCohomology.finrank_submodule_res_extArithLoc_archSlot_eq_zero hp2 S A u ((ZMod p) ∙ z)
        omega
      rw [hx x, hx y]
    haveI := hsub M
    haveI := hsub (M.dualTwist (cycloChar p))
    refine ⟨0, ?_, ?_⟩
    · intro a b _; exact Subsingleton.elim _ _
    · intro f; refine ⟨0, ?_⟩; ext a; have : a = 0 := Subsingleton.elim _ _; subst this; simp only [map_zero]
  choose θu hθubij using hinf
  let θ : ∀ v : extArithIndex S, continuousH1 (extArithLoc S v) (Rep.res (extArithLoc S v) M) →ₗ[ZMod p]
      Module.Dual (ZMod p) (continuousH1 (extArithLoc S v) (Rep.res (extArithLoc S v) (M.dualTwist (cycloChar p)))) :=
    fun v => match v with
      | Sum.inl u => θu u
      | Sum.inr q => θq q
  have hθ : ∀ v, Function.Bijective (θ v) := by
    rintro (u | q)
    · exact hθubij u
    · exact hθqbij q

  haveI hfin2 : FiniteDimensional (ZMod p) (continuousH2S S M) := TWNum.finiteDimensional_continuousH2S S hpS M hsm hMur
  obtain ⟨Fx, hFxS, hreps⟩ := exists_shaConstLevel S M
  obtain ⟨F, instNF, instG, hFS, hFxF, hFM', hFM, hSTAB1, hζF, hpG⟩ :=
    exists_baseLevel S hpS M hsm hMur ζ hζ Fx hFxS
  have hβeq := betaOf_equivariant M F
  have hβ := betaOf_bijective M F hFM'
  have hB := Bof_torsion M F
  let B₀ : Rep ℤ (↥F ≃ₐ[ℚ] ↥F) := Bof M F

  have hLEV_low : ∃ (Fc F₁ : IntermediateField ℚ (AlgebraicClosure ℚ)) (h0c : F ≤ Fc) (hc1 : Fc ≤ F₁)
      (_ : NumberField ↥Fc) (_ : IsGalois ℚ ↥Fc) (_ : NumberField ↥F₁) (_ : IsGalois ℚ ↥F₁),
      Fc.IsUnramifiedOutside S ∧ F₁.IsUnramifiedOutside S ∧
      CapClause (p := p) S F Fc ∧ SepClause S Fc F₁ (Bofπ F M (levelMapR F Fc h0c)) := by
    obtain ⟨Fc, F₁, i1, i2, i3, i4, h0c, hc1, h⟩ := exists_lower_levels S hpS M F hFS
    exact ⟨Fc, F₁, h0c, hc1, i1, i2, i3, i4, h⟩
  obtain ⟨Fc, F₁, h0c, hc1, instNFc, instGc, instNF₁, instG₁, hFcS, hF₁S, hCAP_a, hSEP_b⟩ := hLEV_low
  haveI hle_a : Fact (F ≤ Fc) := ⟨h0c⟩
  haveI hle_b : Fact (Fc ≤ F₁) := ⟨hc1⟩
  have h01 : F ≤ F₁ := h0c.trans hc1
  let πa : (↥Fc ≃ₐ[ℚ] ↥Fc) →* (↥F ≃ₐ[ℚ] ↥F) := levelMapR F Fc h0c
  let πb : (↥F₁ ≃ₐ[ℚ] ↥F₁) →* (↥Fc ≃ₐ[ℚ] ↥Fc) := levelMapR Fc F₁ hc1
  let π₁ : (↥F₁ ≃ₐ[ℚ] ↥F₁) →* (↥F ≃ₐ[ℚ] ↥F) := πa.comp πb
  have hπa : ∀ γ, πa (AlgEquiv.restrictNormalHom ↥Fc γ) = AlgEquiv.restrictNormalHom ↥F γ := levelMapR_restrictNormalHom F Fc h0c
  have hπb : ∀ γ, πb (AlgEquiv.restrictNormalHom ↥F₁ γ) = AlgEquiv.restrictNormalHom ↥Fc γ := levelMapR_restrictNormalHom Fc F₁ hc1
  have hπ₁ : ∀ γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, π₁ (AlgEquiv.restrictNormalHom ↥F₁ γ) = AlgEquiv.restrictNormalHom ↥F γ := fun γ => by
    change πa (πb (AlgEquiv.restrictNormalHom ↥F₁ γ)) = _
    rw [hπb, hπa]
  let Bc : Rep ℤ (↥Fc ≃ₐ[ℚ] ↥Fc) := Rep.res πa B₀
  let B₁ : Rep ℤ (↥F₁ ≃ₐ[ℚ] ↥F₁) := Rep.res π₁ B₀
  letI instBc : Fintype Bc := fintype_Bof M F
  letI instB₁ : Fintype B₁ := fintype_Bof M F
  have hβeq_c : ∀ (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (b : Bc),
      betaOf M F (Bc.ρ (AlgEquiv.restrictNormalHom ↥Fc γ) b) = (M.dualTwist (cycloChar p)).ρ γ (betaOf M F b) :=
    hβeq_res M F Fc πa hπa B₀ (betaOf M F) hβeq
  have hβeq₁ : ∀ (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (b : B₁),
      betaOf M F (B₁.ρ (AlgEquiv.restrictNormalHom ↥F₁ γ) b) = (M.dualTwist (cycloChar p)).ρ γ (betaOf M F b) :=
    hβeq_res M F F₁ π₁ hπ₁ B₀ (betaOf M F) hβeq

  have hFM₁ : ∀ s ∈ F₁.fixingSubgroup, ∀ m : M, M.ρ s m = m :=
    fun s hs m => hFM s (IntermediateField.fixingSubgroup_antitone h01 hs) m
  have hμ₁ : ∀ u : (AlgebraicClosure ℚ)ˣ, u ^ p = 1 → ∃ e : NumberField.SUnits.sUnitsRep ℚ ↥F₁ (Sq S), iotaE F₁ (Sq S) e = Additive.ofMul u :=
    fun u hu => exists_sUnits_of_pow_eq_one S F₁ ζ hζ (h01 hζF) u hu
  obtain ⟨K, F₂, instNK, instGK, instNF₂, instG₂, h1k, hk2, hKS, hF₂S, hKD, hCAP_d⟩ :=
    exists_upper_levels S hpS M ζ hζ F₁ hF₁S hFM₁ B₁ (betaOf M F) hβeq₁ hβ hB hμ₁
  haveI hle_c : Fact (F₁ ≤ K) := ⟨h1k⟩
  haveI hle_d : Fact (K ≤ F₂) := ⟨hk2⟩
  have h12 : F₁ ≤ F₂ := h1k.trans hk2
  let πc : (↥K ≃ₐ[ℚ] ↥K) →* (↥F₁ ≃ₐ[ℚ] ↥F₁) := levelMapR F₁ K h1k
  let πd : (↥F₂ ≃ₐ[ℚ] ↥F₂) →* (↥K ≃ₐ[ℚ] ↥K) := levelMapR K F₂ hk2
  let π₁₂ : (↥F₂ ≃ₐ[ℚ] ↥F₂) →* (↥F₁ ≃ₐ[ℚ] ↥F₁) := πc.comp πd
  have hπc : ∀ γ, πc (AlgEquiv.restrictNormalHom ↥K γ) = AlgEquiv.restrictNormalHom ↥F₁ γ := levelMapR_restrictNormalHom F₁ K h1k
  have hπd : ∀ γ, πd (AlgEquiv.restrictNormalHom ↥F₂ γ) = AlgEquiv.restrictNormalHom ↥K γ := levelMapR_restrictNormalHom K F₂ hk2
  have hπ₁₂ : ∀ γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, π₁₂ (AlgEquiv.restrictNormalHom ↥F₂ γ) = AlgEquiv.restrictNormalHom ↥F₁ γ := fun γ => by
    change πc (πd (AlgEquiv.restrictNormalHom ↥F₂ γ)) = _
    rw [hπd, hπc]
  let BK : Rep ℤ (↥K ≃ₐ[ℚ] ↥K) := Rep.res πc B₁
  let B₂ : Rep ℤ (↥F₂ ≃ₐ[ℚ] ↥F₂) := Rep.res π₁₂ B₁
  letI instBK : Fintype BK := fintype_Bof M F
  letI instB₂ : Fintype B₂ := fintype_Bof M F
  have hβeq₂ : ∀ (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (b : B₂),
      betaOf M F (B₂.ρ (AlgEquiv.restrictNormalHom ↥F₂ γ) b) = (M.dualTwist (cycloChar p)).ρ γ (betaOf M F b) :=
    hβeq_res M F₁ F₂ π₁₂ hπ₁₂ B₁ (betaOf M F) hβeq₁

  haveI : IsTotallyComplex ↥F := isTotallyComplex_of_mem ζ hζ F hp2 hζF
  haveI : IsTotallyComplex ↥Fc := isTotallyComplex_of_mem ζ hζ Fc hp2 (h0c hζF)
  haveI : IsTotallyComplex ↥F₁ := isTotallyComplex_of_mem ζ hζ F₁ hp2 (h01 hζF)
  haveI : IsTotallyComplex ↥K := isTotallyComplex_of_mem ζ hζ K hp2 (h1k (h01 hζF))
  haveI : IsTotallyComplex ↥F₂ := isTotallyComplex_of_mem ζ hζ F₂ hp2 (h12 (h01 hζF))
  have hunr := hunr_F S F hFS
  have hunr_c := hunr_F S Fc hFcS
  have hunr₁ := hunr_F S F₁ hF₁S
  have hunr_k := hunr_F S K hKS
  have hunr₂ := hunr_F S F₂ hF₂S

  obtain ⟨infl, hinflpin, hinj, hinflrange⟩ :=
    groupCohomology.exists_inflate_H1_injective_range_iff_split (M.dualTwist (cycloChar p)) F (Bof M F) (betaOf M F) hβ hβeq
  have hrange : ∀ y : H1 (M.dualTwist (cycloChar p)), y ∈ continuousH1S S (M.dualTwist (cycloChar p)) ↔ ∃ x, infl x = y := by
    intro y
    refine ⟨fun hy => (hinflrange y).mpr (hSTAB1 y hy), fun hx => ?_⟩
    obtain ⟨ny, hny, hconst, _⟩ := (hinflrange y).mp hx
    rw [groupCohomology.mem_continuousH1S_iff]
    exact ⟨ny, ⟨F, hFS, fun γ s hs => hconst γ s hs⟩, hny⟩
  have hθ1 : ∀ q : ↥S, IsTheta1 (extArithLoc S (Sum.inr q))
        (Module.Dual.eval (ZMod p) M :
          Rep.res (extArithLoc S (Sum.inr q)) M →ₗ[ZMod p]
            Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p)) →ₗ[ZMod p]
              ofChar (k := ZMod p) ((cycloChar p).comp (extArithLoc S (Sum.inr q))))
        (localInv p ζ (q : Nat.Primes)) (θ (Sum.inr q)) := fun q => hθq1 q

  let sys₂ : InvSys F₂ := InvSys.stdp p hp2 F₂
  have hiii₂ := InvSys.stdp_iii' p hp2 F₂
  obtain ⟨Jd, hJcont_d, hJF_d, hJeq_d, hJout_d, hJunit_d, hJinf_d, hJloc_d, j_d, hj_d, sysK, hiiiK, hvii_d⟩ :=
    invinfl_sys K F₂ hp2 sys₂ hiii₂
  obtain ⟨Jc, hJcont_c, hJF_c, hJeq_c, hJout_c, hJunit_c, hJinf_c, hJloc_c, j_c, hj_c, sys₁, hiii₁, hvii_c⟩ :=
    invinfl_sys F₁ K hp2 sysK hiiiK
  obtain ⟨Jb, hJcont_b, hJF_b, hJeq_b, hJout_b, hJunit_b, hJinf_b, hJloc_b, j_b, hj_b, sysc, hiiic, hvii_b⟩ :=
    invinfl_sys Fc F₁ hp2 sys₁ hiii₁
  obtain ⟨Ja, hJcont_a, hJF_a, hJeq_a, hJout_a, hJunit_a, hJinf_a, hJloc_a, j_a, hj_a, sys₀, hiii₀, hvii_a⟩ :=
    invinfl_sys F Fc hp2 sysc hiiic

  let jE_a := jE S F Fc Ja hJF_a hJeq_a hJout_a hJunit_a hJinf_a
  let jJ_a := jJ S F Fc Ja hJeq_a hJout_a
  let jY_a := jY S F Fc Ja hJF_a hJeq_a hJout_a hJunit_a hJinf_a
  let jC_a := jC S F Fc Ja hJF_a hJeq_a hJout_a hJunit_a hJinf_a
  let jE_b := jE S Fc F₁ Jb hJF_b hJeq_b hJout_b hJunit_b hJinf_b
  let jJ_b := jJ S Fc F₁ Jb hJeq_b hJout_b
  let jY_b := jY S Fc F₁ Jb hJF_b hJeq_b hJout_b hJunit_b hJinf_b
  let jC_b := jC S Fc F₁ Jb hJF_b hJeq_b hJout_b hJunit_b hJinf_b
  let jE_c := jE S F₁ K Jc hJF_c hJeq_c hJout_c hJunit_c hJinf_c
  let jJ_c := jJ S F₁ K Jc hJeq_c hJout_c
  let jY_c := jY S F₁ K Jc hJF_c hJeq_c hJout_c hJunit_c hJinf_c
  let jC_c := jC S F₁ K Jc hJF_c hJeq_c hJout_c hJunit_c hJinf_c
  let jE_d := jE S K F₂ Jd hJF_d hJeq_d hJout_d hJunit_d hJinf_d
  let jJ_d := jJ S K F₂ Jd hJeq_d hJout_d
  let jY_d := jY S K F₂ Jd hJF_d hJeq_d hJout_d hJunit_d hJinf_d
  let jC_d := jC S K F₂ Jd hJF_d hJeq_d hJout_d hJunit_d hJinf_d

  let jE₁ : Rep.res π₁ (seqF S F).X₁ ⟶ (seqF S F₁).X₁ := (Rep.resFunctor πb).map jE_a ≫ jE_b
  let jJ₁ : Rep.res π₁ (seqF S F).X₂ ⟶ (seqF S F₁).X₂ := (Rep.resFunctor πb).map jJ_a ≫ jJ_b
  let jY₁ : Rep.res π₁ (seqF S F).X₃ ⟶ (seqF S F₁).X₃ := (Rep.resFunctor πb).map jY_a ≫ jY_b
  let jC₁ : Rep.res π₁ (CS S F) ⟶ CS S F₁ := (Rep.resFunctor πb).map jC_a ≫ jC_b
  have hsqE₁ : (Rep.resFunctor π₁).map (seqF S F).f ≫ jJ₁ = jE₁ ≫ (seqF S F₁).f :=
    pasteSq' πa πb (seqF S F).f (seqF S Fc).f (seqF S F₁).f jE_a jJ_a jE_b jJ_b
      (hsqE S F Fc Ja hJF_a hJeq_a hJout_a hJunit_a hJinf_a) (hsqE S Fc F₁ Jb hJF_b hJeq_b hJout_b hJunit_b hJinf_b)
  have hsqY₁ : (Rep.resFunctor π₁).map (seqF S F).g ≫ jY₁ = jJ₁ ≫ (seqF S F₁).g :=
    pasteSq' πa πb (seqF S F).g (seqF S Fc).g (seqF S F₁).g jJ_a jY_a jJ_b jY_b
      (hsqY S F Fc Ja hJF_a hJeq_a hJout_a hJunit_a hJinf_a) (hsqY S Fc F₁ Jb hJF_b hJeq_b hJout_b hJunit_b hJinf_b)
  have hsqC₁ : (Rep.resFunctor π₁).map (RepImage.ι (LF S F)) ≫ jC₁ = jY₁ ≫ RepImage.ι (LF S F₁) :=
    pasteSq' πa πb (RepImage.ι (LF S F)) (RepImage.ι (LF S Fc)) (RepImage.ι (LF S F₁)) jY_a jC_a jY_b jC_b
      (hsqCι S F Fc Ja hJF_a hJeq_a hJout_a hJunit_a hJinf_a) (hsqCι S Fc F₁ Jb hJF_b hJeq_b hJout_b hJunit_b hJinf_b)
  have hjC₁ : ∀ c, invGSFs S F₁ hunr₁ sys₁ ((groupCohomology.map π₁ jC₁ 2).hom c) = invGSFs S F hunr sys₀ c :=
    inv_comp₂ πa πb jC_a jC_b (invGSFs S F hunr sys₀) (invGSFs S Fc hunr_c sysc) (invGSFs S F₁ hunr₁ sys₁)
      (hjC S F Fc hunr hunr_c sys₀ sysc Ja hJF_a hJeq_a hJout_a hJunit_a hJinf_a j_a hj_a hvii_a)
      (hjC S Fc F₁ hunr_c hunr₁ sysc sys₁ Jb hJF_b hJeq_b hJout_b hJunit_b hJinf_b j_b hj_b hvii_b)
  have hjE_a : ∀ x, iotaE Fc (Sq S) (jE_a.hom x) = iotaE F (Sq S) x :=
    fun x => hjE S F Fc Ja hJF_a hJeq_a hJout_a hJunit_a hJinf_a ⟨pPrime p, hpS⟩ hJloc_a x
  have hjE_b : ∀ x, iotaE F₁ (Sq S) (jE_b.hom x) = iotaE Fc (Sq S) x :=
    fun x => hjE S Fc F₁ Jb hJF_b hJeq_b hJout_b hJunit_b hJinf_b ⟨pPrime p, hpS⟩ hJloc_b x
  have hjE₁ : ∀ x, iotaE F₁ (Sq S) (jE₁.hom x) = iotaE F (Sq S) x :=
    fun x => hjE_comp S F Fc F₁ jE_a jE_b hjE_a hjE_b x

  let jE₂ : Rep.res π₁₂ (seqF S F₁).X₁ ⟶ (seqF S F₂).X₁ := (Rep.resFunctor πd).map jE_c ≫ jE_d
  let jJ₂ : Rep.res π₁₂ (seqF S F₁).X₂ ⟶ (seqF S F₂).X₂ := (Rep.resFunctor πd).map jJ_c ≫ jJ_d
  let jY₂ : Rep.res π₁₂ (seqF S F₁).X₃ ⟶ (seqF S F₂).X₃ := (Rep.resFunctor πd).map jY_c ≫ jY_d
  let jC₂ : Rep.res π₁₂ (CS S F₁) ⟶ CS S F₂ := (Rep.resFunctor πd).map jC_c ≫ jC_d
  have hsqE₂ : (Rep.resFunctor π₁₂).map (seqF S F₁).f ≫ jJ₂ = jE₂ ≫ (seqF S F₂).f :=
    pasteSq' πc πd (seqF S F₁).f (seqF S K).f (seqF S F₂).f jE_c jJ_c jE_d jJ_d
      (hsqE S F₁ K Jc hJF_c hJeq_c hJout_c hJunit_c hJinf_c) (hsqE S K F₂ Jd hJF_d hJeq_d hJout_d hJunit_d hJinf_d)
  have hsqY₂ : (Rep.resFunctor π₁₂).map (seqF S F₁).g ≫ jY₂ = jJ₂ ≫ (seqF S F₂).g :=
    pasteSq' πc πd (seqF S F₁).g (seqF S K).g (seqF S F₂).g jJ_c jY_c jJ_d jY_d
      (hsqY S F₁ K Jc hJF_c hJeq_c hJout_c hJunit_c hJinf_c) (hsqY S K F₂ Jd hJF_d hJeq_d hJout_d hJunit_d hJinf_d)
  have hsqC₂ : (Rep.resFunctor π₁₂).map (RepImage.ι (LF S F₁)) ≫ jC₂ = jY₂ ≫ RepImage.ι (LF S F₂) :=
    pasteSq' πc πd (RepImage.ι (LF S F₁)) (RepImage.ι (LF S K)) (RepImage.ι (LF S F₂)) jY_c jC_c jY_d jC_d
      (hsqCι S F₁ K Jc hJF_c hJeq_c hJout_c hJunit_c hJinf_c) (hsqCι S K F₂ Jd hJF_d hJeq_d hJout_d hJunit_d hJinf_d)
  have hjC₂ : ∀ c, invGSFs S F₂ hunr₂ sys₂ ((groupCohomology.map π₁₂ jC₂ 2).hom c) = invGSFs S F₁ hunr₁ sys₁ c :=
    inv_comp₂ πc πd jC_c jC_d (invGSFs S F₁ hunr₁ sys₁) (invGSFs S K hunr_k sysK) (invGSFs S F₂ hunr₂ sys₂)
      (hjC S F₁ K hunr₁ hunr_k sys₁ sysK Jc hJF_c hJeq_c hJout_c hJunit_c hJinf_c j_c hj_c hvii_c)
      (hjC S K F₂ hunr_k hunr₂ sysK sys₂ Jd hJF_d hJeq_d hJout_d hJunit_d hJinf_d j_d hj_d hvii_d)
  have hjE_c : ∀ x, iotaE K (Sq S) (jE_c.hom x) = iotaE F₁ (Sq S) x :=
    fun x => hjE S F₁ K Jc hJF_c hJeq_c hJout_c hJunit_c hJinf_c ⟨pPrime p, hpS⟩ hJloc_c x
  have hjE_d : ∀ x, iotaE F₂ (Sq S) (jE_d.hom x) = iotaE K (Sq S) x :=
    fun x => hjE S K F₂ Jd hJF_d hJeq_d hJout_d hJunit_d hJinf_d ⟨pPrime p, hpS⟩ hJloc_d x
  have hjE₂ : ∀ x, iotaE F₂ (Sq S) (jE₂.hom x) = iotaE F₁ (Sq S) x :=
    fun x => hjE_comp S F₁ K F₂ jE_c jE_d hjE_c hjE_d x

  obtain ⟨infl₁, hinflpin₁, hinj₁, hinflrange₁⟩ :=
    groupCohomology.exists_inflate_H1_injective_range_iff_split (M.dualTwist (cycloChar p)) F₁ B₁ (betaOf M F) hβ hβeq₁
  obtain ⟨infl₂, hinflpin₂, hinj₂, hinflrange₂⟩ :=
    groupCohomology.exists_inflate_H1_injective_range_iff_split (M.dualTwist (cycloChar p)) F₂ B₂ (betaOf M F) hβ hβeq₂
  have hSTAB1₁ : ∀ y : H1 (M.dualTwist (cycloChar p)), y ∈ continuousH1S S (M.dualTwist (cycloChar p)) →
      ∃ ny : cocycles₁ (M.dualTwist (cycloChar p)), (H1π (M.dualTwist (cycloChar p))).hom ny = y ∧
        (∀ (γ s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), s ∈ F₁.fixingSubgroup → ny (γ * s) = ny γ) ∧
        (∀ s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, s ∈ F₁.fixingSubgroup → ny s = 0) := fun y hy => by
    obtain ⟨ny, h1, h2, h3⟩ := hSTAB1 y hy
    exact ⟨ny, h1, fun γ s hs => h2 γ s (IntermediateField.fixingSubgroup_antitone h01 hs),
      fun s hs => h3 s (IntermediateField.fixingSubgroup_antitone h01 hs)⟩
  have hrange₁ := hrange_of_le (S := S) (M := M) (F := F) (F₁ := F₁) (hle := h01) (hF₁S := hF₁S) (π := π₁) (B := B₀)
    infl₁ hinflrange₁ hSTAB1
  have hrange₂ := hrange_of_le (S := S) (M := M) (F := F₁) (F₁ := F₂) (hle := h12) (hF₁S := hF₂S) (π := π₁₂) (B := B₁)
    infl₂ hinflrange₂ hSTAB1₁

  have hSTAB : ∀ c : continuousH2S S M, c ∈ sha₂ S M →
      ∃ x, LE2' S hpS M ζ hζ F hFS B₀ (betaOf M F) hβeq hβ hB x = c :=
    hSTAB_dock S hpS M ζ hζ F hFS hζF hFM B₀ (betaOf M F) hβeq hβ hB Fx hreps hFxF
  have hLOC₀ := hLOC_s S M ζ hζ F hζF hunr sys₀ hiii₀ B₀ (betaOf M F) hβeq hβ hB hp2 θ hθ1 hloc infl hinflpin
  have hLOC₂ := hLOC_s S M ζ hζ F₂ (h12 (h01 hζF)) hunr₂ sys₂ hiii₂ B₂ (betaOf M F) hβeq₂ hβ hB hp2 θ hθ1 hloc infl₂ hinflpin₂
  have hKERLOC := fun x h => hKERLOC_F S hpS M ζ hζ F hFS hζF B₀ (betaOf M F) hβeq hβ hB hp2 x h

  have hiCj₁ := hiCj (S := S) (F := F) (F₁ := F₁) (π := π₁) (B := B₀) (jY := jY₁) (jC := jC₁) (hsqC := hsqC₁)
  have hid₁ := hid (S := S) (F := F) (F₁ := F₁) (π := π₁) (B := B₀) (jE := jE₁) (jJ := jJ₁) (jY := jY₁) (hsqE := hsqE₁) (hsqY := hsqY₁)
  have hiL₁ := hiL (S := S) (hpS := hpS) (M := M) (ζ := ζ) (hζ := hζ) (F := F) (F₁ := F₁) (hle := h01) (hFS := hFS) (hF₁S := hF₁S)
    (π := π₁) (hπ := hπ₁) (B := B₀) (β := betaOf M F) (hβeq := hβeq) (hβ := hβ) (hB := hB) (jE := jE₁) (hjE := hjE₁)
  have hial₁ := hial_of_hal (S := S) (F := F) (F₁ := F₁) (π := π₁) (B := B₀) (jC := jC₁)
    (al := alFs S F hunr sys₀ B₀ hB) (al₁ := alFs S F₁ hunr₁ sys₁ B₁ hB)
    (inv := invGSFs S F hunr sys₀) (inv₁ := invGSFs S F₁ hunr₁ sys₁)
    (hal := alFs_hal S F hunr sys₀ B₀ hB) (hal₁ := alFs_hal S F₁ hunr₁ sys₁ B₁ hB) (hjCinv := hjC₁)
  have hiB₁ := inflH1_surjective (S := S) (M := M) (F := F) (F₁ := F₁) (π := π₁) (hπ := hπ₁) (B := B₀) (β := betaOf M F) (hβeq := hβeq)
    infl infl₁ hinflpin hinflpin₁ hrange hrange₁ hinj₁

  have hEXF : ∀ φ : Rep.relationModuleInt B₀ ⟶ CS S F,
      (∃ χ : Rep.free ℤ (↥F₁ ≃ₐ[ℚ] ↥F₁) B₁ ⟶ CS S F₁, inflHom π₁ B₀ jC₁ φ = Rep.relationModuleInt.ι B₁ ≫ χ) ∨
      (∃ x : ↥(groupCohomology B₁ 1), alFs S F₁ hunr₁ sys₁ B₁ hB (inflHom π₁ B₀ jC₁ φ) x ≠ 0) := by
    intro φ
    rcases hEXF_comp S M F Fc F₁ hunr₁ sys₁ πa πb hπb jC_a jC_b hSEP_b 1 (fun a ha => by simpa using ha) φ with h | ⟨x, hx⟩
    · exact Or.inl h
    · exact Or.inr ⟨x, by simpa using hx⟩
  have hPITco : ∀ φ : Rep.relationModuleInt B₀ ⟶ CS S F, ∃ (t : Rep.relationModuleInt B₁ ⟶ (seqF S F₁).X₃)
      (χ : Rep.free ℤ (↥F₁ ≃ₐ[ℚ] ↥F₁) B₁ ⟶ CS S F₁), inflHom π₁ B₀ jC₁ φ = t ≫ RepImage.ι (LF S F₁) + Rep.relationModuleInt.ι B₁ ≫ χ :=
    fun φ => hPITco_comp S F Fc F₁ Ja hJF_a hJeq_a hJout_a hJunit_a hJinf_a hJcont_a hJloc_a Jb hJF_b hJeq_b hJout_b hJunit_b hJinf_b hCAP_a B₀ hB φ
  have hαext₁ := alFs_ι_comp S F₁ hunr₁ sys₁ B₁ hB
  have hLESe₁ := map_iEJ_dY' S F₁ B₁
  have hKERLOC₁ := fun x hx v => hKERLOC'_F S hpS M ζ hζ F₁ hF₁S (h01 hζF) B₁ (betaOf M F) hβeq₁ hβ hB hp2 x hx v

  have hiCj₂ := hiCj (S := S) (F := F₁) (F₁ := F₂) (π := π₁₂) (B := B₁) (jY := jY₂) (jC := jC₂) (hsqC := hsqC₂)
  have hid₂ := hid (S := S) (F := F₁) (F₁ := F₂) (π := π₁₂) (B := B₁) (jE := jE₂) (jJ := jJ₂) (jY := jY₂) (hsqE := hsqE₂) (hsqY := hsqY₂)
  have hiL₂ := hiL (S := S) (hpS := hpS) (M := M) (ζ := ζ) (hζ := hζ) (F := F₁) (F₁ := F₂) (hle := h12) (hFS := hF₁S) (hF₁S := hF₂S)
    (π := π₁₂) (hπ := hπ₁₂) (B := B₁) (β := betaOf M F) (hβeq := hβeq₁) (hβ := hβ) (hB := hB) (jE := jE₂) (hjE := hjE₂)
  have hial₂ := hial_of_hal (S := S) (F := F₁) (F₁ := F₂) (π := π₁₂) (B := B₁) (jC := jC₂)
    (al := alFs S F₁ hunr₁ sys₁ B₁ hB) (al₁ := alFs S F₂ hunr₂ sys₂ B₂ hB)
    (inv := invGSFs S F₁ hunr₁ sys₁) (inv₁ := invGSFs S F₂ hunr₂ sys₂)
    (hal := alFs_hal S F₁ hunr₁ sys₁ B₁ hB) (hal₁ := alFs_hal S F₂ hunr₂ sys₂ B₂ hB) (hjCinv := hjC₂)
  have hiB₂ := inflH1_surjective (S := S) (M := M) (F := F₁) (F₁ := F₂) (π := π₁₂) (hπ := hπ₁₂) (B := B₁) (β := betaOf M F) (hβeq := hβeq₁)
    infl₁ infl₂ hinflpin₁ hinflpin₂ hrange₁ hrange₂ hinj₂
  have hinfl : ∀ x, infl₂ (inflH1 π₁₂ B₁ (inflH1 π₁ B₀ x)) = infl x := fun x =>
    (infl_inflH1 (M := M) (F := F₁) (F₁ := F₂) (π := π₁₂) (hπ := hπ₁₂) (B := B₁) (β := betaOf M F) (hβeq := hβeq₁)
      infl₁ infl₂ hinflpin₁ hinflpin₂ _).trans
      (infl_inflH1 (M := M) (F := F) (F₁ := F₁) (π := π₁) (hπ := hπ₁) (B := B₀) (β := betaOf M F) (hβeq := hβeq)
        infl infl₁ hinflpin hinflpin₁ x)

  have hPITker : ∀ (t : Rep.relationModuleInt B₁ ⟶ (seqF S F₁).X₃) (χ : Rep.free ℤ (↥F₁ ≃ₐ[ℚ] ↥F₁) B₁ ⟶ CS S F₁),
      t ≫ RepImage.ι (LF S F₁) = Rep.relationModuleInt.ι B₁ ≫ χ →
      ∃ χ' : Rep.free ℤ (↥F₂ ≃ₐ[ℚ] ↥F₂) B₂ ⟶ (seqF S F₂).X₃, inflHom π₁₂ B₁ jY₂ t = Rep.relationModuleInt.ι B₂ ≫ χ' :=
    fun t χ h => hPITker_comp S F₁ K F₂ Jc hJF_c hJeq_c hJout_c hJunit_c hJinf_c Jd hJF_d hJeq_d hJout_d hJunit_d hJinf_d hJcont_d hJloc_d hCAP_d B₁ hB t χ h
  have hB3ker : ∀ x : H1 ((ihom (Rep.relationModuleInt B₁)).obj (seqF S F₁).X₁),
      LE2' S hpS M ζ hζ F₁ hF₁S B₁ (betaOf M F) hβeq₁ hβ hB x = 0 → inflExt1 π₁₂ B₁ jE₂ x = 0 :=
    Reduce95.KD.hB3ker_of_KDClause S hpS M ζ hζ F₁ hF₁S B₁ (betaOf M F) hβeq₁ hβ hB hKD F₂ hk2 π₁₂ hπ₁₂ jE₂ hjE₂
  have hLESd₂ := dY'_add_ι_comp S F₂ B₂

  exact groupCohomology.exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_assembly S M θ hθ hloc

    (Rep.relationModuleInt.ι B₀) (seqF S F).X₁ (seqF S F).X₂ (seqF S F).X₃ (CS S F)
    (seqF S F).f (seqF S F).g (RepImage.ι (LF S F))
    ↥(groupCohomology B₀ 1)
    (dY' S F B₀) (LE2' S hpS M ζ hζ F hFS B₀ (betaOf M F) hβeq hβ hB)
    (LJ1 S M ζ hζ F hζF B₀ (betaOf M F) hβeq hβ hB) (alFs S F hunr sys₀ B₀ hB)
    infl hinj hrange (hLESa' S F B₀) (hLESb' S F B₀) (hLESc' S F B₀) hKERLOC hSTAB
    (LJ1_surjective S M ζ hζ F hζF B₀ (betaOf M F) hβeq hβ hB) (uVp S ζ hζ)
    (hIDs S M ζ hζ F hζF hunr sys₀ B₀ (betaOf M F) hβeq hβ hB θ hloc infl (uVp S ζ hζ) hLOC₀)
    (fun g => alFs_surjective S F hunr sys₀ B₀ hB hpG g)

    (Rep.relationModuleInt.ι B₁) (seqF S F₁).X₁ (seqF S F₁).X₂ (seqF S F₁).X₃ (CS S F₁)
    (seqF S F₁).f (RepImage.ι (LF S F₁))
    ↥(groupCohomology B₁ 1)
    (dY' S F₁ B₁) (LE2' S hpS M ζ hζ F₁ hF₁S B₁ (betaOf M F) hβeq₁ hβ hB) (alFs S F₁ hunr₁ sys₁ B₁ hB)
    (inflHom π₁ B₀ jY₁) (inflHom π₁ B₀ jC₁) (inflExt1 π₁ B₀ jE₁) (inflH1 π₁ B₀)
    hiB₁ hiCj₁ hid₁ hiL₁ hial₁
    hEXF hPITco hαext₁ hLESe₁ hKERLOC₁

    (Rep.relationModuleInt.ι B₂) (seqF S F₂).X₁ (seqF S F₂).X₂ (seqF S F₂).X₃ (CS S F₂)
    (seqF S F₂).f (seqF S F₂).g (RepImage.ι (LF S F₂))
    ↥(groupCohomology B₂ 1)
    (dY' S F₂ B₂) (LE2' S hpS M ζ hζ F₂ hF₂S B₂ (betaOf M F) hβeq₂ hβ hB)
    (LJ1 S M ζ hζ F₂ (h12 (h01 hζF)) B₂ (betaOf M F) hβeq₂ hβ hB) (alFs S F₂ hunr₂ sys₂ B₂ hB)
    (inflHom π₁₂ B₁ jY₂) (inflHom π₁₂ B₁ jC₂) (inflExt1 π₁₂ B₁ jE₂) (inflH1 π₁₂ B₁)
    hiB₂ hiCj₂ hid₂ hiL₂ hial₂
    hPITker hB3ker (hLESb' S F₂ B₂) hLESd₂ (uVp S ζ hζ)
    (hIDs' S M ζ hζ F₂ (h12 (h01 hζF)) hunr₂ sys₂ B₂ (betaOf M F) hβeq₂ hβ hB θ hloc infl₂ (uVp S ζ hζ) hLOC₂
      infl ((inflH1 π₁₂ B₁).comp (inflH1 π₁ B₀)) hinfl)

end S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two
end P2MW
export P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two (solution)
