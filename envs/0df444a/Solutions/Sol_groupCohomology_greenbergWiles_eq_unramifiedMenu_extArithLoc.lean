-- Prove2me | solution 1 for groupCohomology.greenbergWiles_eq_unramifiedMenu_extArithLoc
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/a5917da8-ef51-57b0-8945-f792ca6e6da5

import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GroupCohomology_SelmerAdm
import Definitions.Def_GroupCohomology_ContinuousDuality
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Theorems.Thm_groupCohomology_greenbergWilesLeAdm_extArithLoc_of_isTheta1_eval_of_ne_two
import Theorems.Thm_groupCohomology_eq_continuousH1S_of_forall_mem_iff
import Theorems.Thm_groupCohomology_finiteDimensional_continuousH1S
import Theorems.Thm_groupCohomology_mem_orthogonal_iff_of_agree_on_continuous
import Theorems.Thm_groupCohomology_theta1_nondegenerate_of_bijective
import Theorems.Thm_groupCohomology_locRes_extArithLoc_apply_mem_continuousH1
import Theorems.Thm_TWNum_subsingleton_H1_extArithLoc_inl_dualTwist
import Theorems.Thm_groupCohomology_exists_localDualityPackage_res_dualTwist_extArithLoc

import Definitions.Def_GroupCohomology_ContinuousH1
import Theorems.Thm_groupCohomology_finrank_finiteQuotientH1_eq_invariants_add_dualTwist_of_primeLocal_ne
import Theorems.Thm_groupCohomology_finrank_finiteQuotientH1_eq_invariants_add_dualTwist_add_finrank_of_primeLocal
import Theorems.Thm_groupCohomology_finiteDimensional_continuousH1_of_isOpen_of_primeLocal
import Theorems.Thm_groupCohomology_map_apply_mem_continuousH1_comp
import Theorems.Thm_groupCohomology_injective_H1_restriction_of_isUnit_index
import Theorems.Thm_groupCohomology_finrank_submodule_res_extArithLoc_archSlot_eq_zero
import Theorems.Thm_ExtCitation_finrank_unramifiedContinuousClasses_eq_finrank_invariants
import Theorems.Thm_Rep_finrank_invariants_res_dualTwist_eq
import Theorems.Thm_Rep_dualTwist_cycloChar_smooth
import Theorems.Thm_Rep_nonempty_dualTwist_dualTwist_iso
import Theorems.Thm_groupCohomology_finrank_invariants_archimedean_add_dualTwist_add_H1_eq
import Theorems.Thm_TWNum_finrank_continuousH2_extArithLoc_inl_eq_zero
import Theorems.Thm_groupCohomology_theta1_apply_eq_zero_of_mem_unramified_of_mem_unramified
import Theorems.Thm_Rep_dualTwist_cycloChar_unramifiedOutside
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_greenbergWiles_eq_unramifiedMenu_extArithLoc
p2m_attr_erase "instance" "M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion NumberField.AdelicHaar.locallyCompactSpace_adeleRing NumberField.AdelicHaar.finite_residueField_adicCompletionIntegers NumberField.AdelicHaar.locallyCompactSpace_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_finiteAdeleRing NumberField.AdelicHaar.compactSpace_adicCompletionIntegers NumberField.AdelicHaar.t2Space_finiteAdeleRing NumberField.AdelicHaar.t2Space_matrix_adeleRing NumberField.AdelicHaar.t2Space_adeleRing NumberField.AdelicHaar.fact_isOpen_adicCompletionIntegers NumberField.AdelicHaar.t2Space_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_matrix_adeleRing NumberField.AdelicHaar.t2Space_infiniteAdeleRing NumberField.AdelicHaar.properSpace_adicCompletion M4aHerbrand.Bridge.instT2SpaceAdeleRing LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite"
p2m_attr_erase "instance" "Deep.NTSupply.instNormalRayClassSubgroup instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal AlgebraicClosure.Rat.isGalois groupCohomology.Kummer.instMulDistribMulActionRootsOfUnity groupCohomology.normal_comap_fixingSubgroup groupCohomology.finiteIndex_comap_fixingSubgroup Rep.relationCarrier.instAddCommGroup NumberField.LevelArith.instCommGroupUnitsModPow groupCohomology.instMulDistribMulActionGaloisSUnits"
p2m_attr_erase "simp" "groupCohomology.unitsInflate₁_apply groupCohomology.unitsInflate₂_apply M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk M4aHerbrand.IdeleGaloisDescent.classAct_mk M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq ExtCitation.LocalLevel.coe_smul_OO WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl NumberField.SUnits.val_zsmul NumberField.SUnits.val_add M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply"
p2m_attr_erase "simp" "FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq M4aHerbrand.Bridge.finiteConorm_apply SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul"
p2m_attr_erase "simp" "TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply"
p2m_attr_erase "simp" "RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq IsLocalRing.principalUnits_zero Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec groupCohomology.Kummer.coe_kummerCocycleRoots groupCohomology.Kummer.mem_powerSubgroup_iff groupCohomology.Kummer.val_smul_units groupCohomology.Kummer.kummerHom_apply groupCohomology.Kummer.coe_smul_rootsOfUnity"
p2m_attr_erase "simp" "groupCohomology.levelQuotientEquiv_mk groupCohomology.levelQuotientHom_mk Rep.toIntRepρ_apply_apply Rep.toIntRep_ρ Rep.toIntRepMap_hom_apply M4aHerbrand.AdeleBaseChange.classNorm_mk M4aHerbrand.AdeleBaseChange.coe_idelesMap_apply M4aHerbrand.AdeleBaseChange.classMap_mk M4aHerbrand.repHomResOfMulEquivariant_hom_apply M4aHerbrand.AdeleBaseChange.sClassNorm_mk M4aHerbrand.AdeleBaseChange.sClassMap_mk NumberField.SArchIdele.fibre_inl NumberField.SArchIdele.toSIdele_hom_apply_inr NumberField.SArchIdele.toSIdele_hom_apply_inl_inr NumberField.SArchIdele.toSIdele_hom_apply_inl_inl NumberField.SArchIdele.fibre_inr Representation.TateResCor.cosetDecomp_apply Rep.coe_tateHneg1Res_apply Representation.TateResCor.coe_tateHneg1Cores_apply Representation.TateResCor.tateH0Res_mk Rep.coe_tateHneg1Cores_apply Rep.tateH0Res_mk Representation.TateResCor.coe_cosetNormInvariants_apply Rep.tateH0Cores_mk Representation.TateResCor.coinvariantsCores_mk Representation.TateResCor.coinvariantsTransfer_mk Representation.TateResCor.tateH0Cores_mk Representation.TateResCor.coe_tateHneg1Res_apply Rep.coe_tateδneg2_apply Rep.splittingShortComplex_X₃ Rep.splittingShortComplex_X₁ Rep.splittingShortComplex_X₂ Rep.splittingShortComplex_f Rep.augShortComplex_f Rep.augShortComplex_X₃ Rep.cocycleTwist_single Rep.augShortComplex_X₂ Rep.splittingModuleι_hom_apply Rep.augShortComplex_X₁ Rep.splittingShortComplex_g"
p2m_attr_erase "simp" "Rep.augShortComplex_g Rep.splittingModuleπ_hom_apply Rep.coe_dimShiftDownObjMap_apply groupCohomology.continuousH2Inflation_H2π groupCohomology.levelInflate₂_apply groupCohomology.coe_levelInflateCocycles₂ groupCohomology.levelInflate₁_apply NumberField.LevelArith.coe_levelFieldEquiv NumberField.LevelArith.modP_apply_mk NumberField.LevelArith.coe_levelFieldEquiv_symm NumberField.LevelArith.torsionP_apply_coe NumberField.LevelArith.repTorsionPMap_hom_apply_coe NumberField.LevelArith.toZMod_apply NumberField.LevelArith.repModPMap_hom_mk groupCohomology.coe_continuousH1SrMap_apply groupCohomology.continuousH2SrMap_continuousH2Srπ groupCohomology.coe_levelCocyclesSr₂Map NumberField.LevelArith.smul_mk NumberField.LevelArith.selmerRepInt_ρ_apply NumberField.LevelArith.selmerRepField_ρ_apply NumberField.LevelArith.unitsModPowMap_mk groupCohomology.frobeniusOnCoinvariants_mk groupCohomology.evalAtGen_apply Rep.quotientRightTranslation_hom_single Rep.quotientRightTranslationTwist_hom_apply groupCohomology.coe_smul_galoisSUnits groupCohomology.galoisSUnitsToUnits_apply"

set_option autoImplicit false
open CategoryTheory Module groupCohomology ExtCitation

universe u

private theorem selmerAdm_dualConditions_le_selmerAdm_menu
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes)
    (M M' : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (pairing : ∀ v : extArithIndex S,
      H1 (Rep.res (extArithLoc S v) M) →ₗ[ZMod p] H1 (Rep.res (extArithLoc S v) M') →ₗ[ZMod p] ZMod p)
    (L : ∀ v, Submodule (ZMod p) (H1 (Rep.res (extArithLoc S v) M)))
    (L' : ∀ v, Submodule (ZMod p) (H1 (Rep.res (extArithLoc S v) M')))
    (adm' : Submodule (ZMod p) (H1 M'))
    (hadm'cts : ∀ x ∈ adm', ∀ v, (locRes (extArithLoc S) M' v).hom x ∈
      continuousH1 (extArithLoc S v) (Rep.res (extArithLoc S v) M'))
    (hdual : ∀ v, ∀ y : H1 (Rep.res (extArithLoc S v) M'),
      y ∈ continuousH1 (extArithLoc S v) (Rep.res (extArithLoc S v) M') →
        y ∈ dualConditions (extArithLoc S) M M' pairing L v → y ∈ L' v) :
    selmerAdm (extArithLoc S) M' (dualConditions (extArithLoc S) M M' pairing L) adm' ≤
      selmerAdm (extArithLoc S) M' L' adm' := by
  intro x hx
  rw [mem_selmerAdm_iff] at hx ⊢
  exact ⟨fun v => hdual v _ (hadm'cts x hx.2 v) (hx.1 v), hx.2⟩

private theorem le_menu_of_greenbergWilesLeAdm
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes)
    (M M' : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (pairing : ∀ v : extArithIndex S,
      H1 (Rep.res (extArithLoc S v) M) →ₗ[ZMod p] H1 (Rep.res (extArithLoc S v) M') →ₗ[ZMod p] ZMod p)
    (L : ∀ v, Submodule (ZMod p) (H1 (Rep.res (extArithLoc S v) M)))
    (L' : ∀ v, Submodule (ZMod p) (H1 (Rep.res (extArithLoc S v) M')))
    (adm : Submodule (ZMod p) (H1 M)) (adm' : Submodule (ZMod p) (H1 M'))
    [FiniteDimensional (ZMod p) adm']
    (hadm'cts : ∀ x ∈ adm', ∀ v, (locRes (extArithLoc S) M' v).hom x ∈
      continuousH1 (extArithLoc S v) (Rep.res (extArithLoc S v) M'))
    (hdual : ∀ v, ∀ y : H1 (Rep.res (extArithLoc S v) M'),
      y ∈ continuousH1 (extArithLoc S v) (Rep.res (extArithLoc S v) M') →
        y ∈ dualConditions (extArithLoc S) M M' pairing L v → y ∈ L' v)
    (hle : greenbergWilesLeAdm (extArithLoc S) M M' pairing L adm adm') :
    finrank (ZMod p) (selmerAdm (extArithLoc S) M L adm) + finrank (ZMod p) M'.ρ.invariants
        + ∑ v, finrank (ZMod p) (Rep.res (extArithLoc S v) M).ρ.invariants
      ≤ finrank (ZMod p) (selmerAdm (extArithLoc S) M' L' adm') + finrank (ZMod p) M.ρ.invariants
        + ∑ v, finrank (ZMod p) (L v) := by
  unfold greenbergWilesLeAdm at hle
  have hmono := Submodule.finrank_mono
    (selmerAdm_dualConditions_le_selmerAdm_menu S M M' pairing L L' adm' hadm'cts hdual)
  omega

private theorem finiteDimensional_and_locRes_mem_continuousH1_of_adm
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes)
    (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) [FiniteDimensional (ZMod p) M]
    (hsm : ∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s ∈ F.fixingSubgroup, M.ρ s m = m)
    (hMur : ∀ q : Nat.Primes, q ∉ S → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
      A.LiesOverPrime (q : ℕ) → ∀ g ∈ A.inertiaSubgroupIn ℚ, M.ρ g = 1)
    (adm : Submodule (ZMod p) (H1 M))
    (hadm : ∀ x : H1 M, x ∈ adm ↔
      ∃ c : cocycles₁ M, IsLocallyConstant ⇑c ∧
        (∀ q : Nat.Primes, q ∉ S → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
          A.LiesOverPrime (q : ℕ) → ∃ m : M, ∀ g ∈ A.inertiaSubgroupIn ℚ, c g = M.ρ g m - m) ∧
        H1π M c = x) :
    FiniteDimensional (ZMod p) adm ∧
      ∀ x ∈ adm, ∀ v, (locRes (extArithLoc S) M v).hom x ∈
        continuousH1 (extArithLoc S v) (Rep.res (extArithLoc S v) M) := by
  have hS : adm = continuousH1S S M := eq_continuousH1S_of_forall_mem_iff S M hMur adm hadm
  subst hS
  refine ⟨finiteDimensional_continuousH1S S M hsm, fun x hx v => ?_⟩
  exact locRes_extArithLoc_apply_mem_continuousH1 S M x (continuousH1S_le_continuousH1 S M hx) v

section Transport

private noncomputable def H1congr {k Γ : Type} [Field k] [Group Γ] {A B : Rep k Γ} (e : A ≅ B) :
    H1 A ≃ₗ[k] H1 B :=
  ((groupCohomology.functor k Γ 1).mapIso e).toLinearEquiv

private theorem H1congr_apply {k Γ : Type} [Field k] [Group Γ] {A B : Rep k Γ} (e : A ≅ B) (x : H1 A) :
    H1congr e x = (map (MonoidHom.id Γ) e.hom 1).hom x :=
  rfl

private theorem H1congr_symm_apply_apply {k Γ : Type} [Field k] [Group Γ] {A B : Rep k Γ} (e : A ≅ B)
    (x : H1 A) : H1congr e.symm (H1congr e x) = x :=
  ModuleCat.inv_hom_apply ((groupCohomology.functor k Γ 1).mapIso e) x

private theorem H1congr_apply_symm_apply {k Γ : Type} [Field k] [Group Γ] {A B : Rep k Γ} (e : A ≅ B)
    (y : H1 B) : H1congr e (H1congr e.symm y) = y :=
  ModuleCat.hom_inv_apply ((groupCohomology.functor k Γ 1).mapIso e) y

private noncomputable def cocycles₁congr {k Γ : Type} [Field k] [Group Γ] {A B : Rep k Γ} (e : A ≅ B)
    (c : cocycles₁ A) : cocycles₁ B :=
  mapCocycles₁ (MonoidHom.id Γ) e.hom c

private theorem cocycles₁congr_apply {k Γ : Type} [Field k] [Group Γ] {A B : Rep k Γ} (e : A ≅ B)
    (c : cocycles₁ A) (g : Γ) : (cocycles₁congr e c : Γ → B) g = e.hom.hom (c g) :=
  rfl

private theorem H1congr_H1π {k Γ : Type} [Field k] [Group Γ] {A B : Rep k Γ} (e : A ≅ B)
    (c : cocycles₁ A) : H1congr e (H1π A c) = H1π B (cocycles₁congr e c) :=
  H1π_comp_map_apply (MonoidHom.id Γ) e.hom c

private theorem locRes_H1congr {k Γ : Type} [Field k] [Group Γ] {ι : Type} {Γv : ι → Type}
    [∀ v, Group (Γv v)] (loc : ∀ v, Γv v →* Γ) {A B : Rep k Γ} (e : A ≅ B) (v : ι) (x : H1 A) :
    (locRes loc B v).hom (H1congr e x)
      = H1congr ((Rep.resFunctor (loc v)).mapIso e) ((locRes loc A v).hom x) := by
  exact congrArg (fun T => T.hom x) ((resNatTrans (k := k) (loc v) 1).naturality e.hom)

private theorem finrank_invariants_congr {k Γ : Type} [Field k] [Group Γ] {A B : Rep k Γ} (e : A ≅ B) :
    finrank k A.ρ.invariants = finrank k B.ρ.invariants :=
  ((Rep.invariantsFunctor k Γ).mapIso e).toLinearEquiv.finrank_eq

private noncomputable def condCongr {k Γ : Type} [Field k] [Group Γ] {ι : Type} {Γv : ι → Type}
    [∀ v, Group (Γv v)] (loc : ∀ v, Γv v →* Γ) {A B : Rep k Γ} (e : A ≅ B)
    (L : ∀ v, Submodule k (H1 (Rep.res (loc v) A))) (v : ι) : Submodule k (H1 (Rep.res (loc v) B)) :=
  (L v).map (H1congr ((Rep.resFunctor (loc v)).mapIso e)).toLinearMap

private theorem finrank_condCongr {k Γ : Type} [Field k] [Group Γ] {ι : Type} {Γv : ι → Type}
    [∀ v, Group (Γv v)] (loc : ∀ v, Γv v →* Γ) {A B : Rep k Γ} (e : A ≅ B)
    (L : ∀ v, Submodule k (H1 (Rep.res (loc v) A))) (v : ι) :
    finrank k (condCongr loc e L v) = finrank k (L v) :=
  LinearEquiv.finrank_map_eq _ _

private theorem map_selmerAdm_H1congr {k Γ : Type} [Field k] [Group Γ] {ι : Type} [Fintype ι]
    {Γv : ι → Type} [∀ v, Group (Γv v)] (loc : ∀ v, Γv v →* Γ) {A B : Rep k Γ} (e : A ≅ B)
    (L : ∀ v, Submodule k (H1 (Rep.res (loc v) A))) (adm : Submodule k (H1 A)) :
    (selmerAdm loc A L adm).map (H1congr e).toLinearMap
      = selmerAdm loc B (condCongr loc e L) (adm.map (H1congr e).toLinearMap) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, mem_selmerAdm_iff] at hx
    rw [mem_selmerAdm_iff]
    refine ⟨fun v => ?_, Submodule.mem_map_of_mem hx.2⟩
    rw [LinearEquiv.coe_coe, locRes_H1congr]
    exact Submodule.mem_map_of_mem (hx.1 v)
  · intro hy
    rw [mem_selmerAdm_iff] at hy
    obtain ⟨x', hx', hx'y⟩ := hy.2
    refine ⟨x', ?_, hx'y⟩
    rw [SetLike.mem_coe, mem_selmerAdm_iff]
    refine ⟨fun v => ?_, hx'⟩
    obtain ⟨z, hz, hzy⟩ := hy.1 v
    have hinj := (H1congr ((Rep.resFunctor (loc v)).mapIso e)).injective
    have hxy : H1congr e x' = y := hx'y
    have key : H1congr ((Rep.resFunctor (loc v)).mapIso e) ((locRes loc A v).hom x')
        = H1congr ((Rep.resFunctor (loc v)).mapIso e) z := by
      rw [← locRes_H1congr, hxy]
      exact hzy.symm
    rw [hinj key]
    exact hz

private theorem finrank_selmerAdm_congr {k Γ : Type} [Field k] [Group Γ] {ι : Type} [Fintype ι]
    {Γv : ι → Type} [∀ v, Group (Γv v)] (loc : ∀ v, Γv v →* Γ) {A B : Rep k Γ} (e : A ≅ B)
    (L : ∀ v, Submodule k (H1 (Rep.res (loc v) A))) (adm : Submodule k (H1 A)) :
    finrank k (selmerAdm loc A L adm)
      = finrank k (selmerAdm loc B (condCongr loc e L) (adm.map (H1congr e).toLinearMap)) := by
  rw [← map_selmerAdm_H1congr, LinearEquiv.finrank_map_eq]

private abbrev GlobalClause (S : Finset Nat.Primes) {p : ℕ} [Fact p.Prime]
    (A : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (x : H1 A) : Prop :=
  ∃ c : cocycles₁ A, IsLocallyConstant ⇑c ∧
    (∀ q : Nat.Primes, q ∉ S → ∀ A' : ValuationSubring (AlgebraicClosure ℚ),
      A'.LiesOverPrime (q : ℕ) → ∃ m : A, ∀ g ∈ A'.inertiaSubgroupIn ℚ, c g = A.ρ g m - m) ∧
    H1π A c = x

private abbrev ContinuityClause {k H : Type} [Field k] [Group H]
    (r : H →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (A : Rep k H) (x : H1 A) : Prop :=
  ∃ c : cocycles₁ A,
    (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ g s, r s ∈ F.fixingSubgroup → c.val (g * s) = c.val g) ∧
    H1π _ c = x

private abbrev UnramifiedClause {k H : Type} [Field k] [Group H]
    (r : H →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (I : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (A : Rep k H) (x : H1 A) : Prop :=
  ∃ c : cocycles₁ A,
    (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ g s, r s ∈ F.fixingSubgroup → c.val (g * s) = c.val g) ∧
    (∃ m : A, ∀ s, r s ∈ I → c.val s = A.ρ s m - m) ∧
    H1π _ c = x

private theorem globalClause_map (S : Finset Nat.Primes) {p : ℕ} [Fact p.Prime]
    {A B : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)} (e : A ≅ B) (x : H1 A)
    (hx : GlobalClause S A x) : GlobalClause S B (H1congr e x) := by
  obtain ⟨c, hlc, hur, hcx⟩ := hx
  refine ⟨cocycles₁congr e c, ?_, ?_, by rw [← hcx, H1congr_H1π]⟩
  · have hcomp : (⇑(cocycles₁congr e c) : _ → B) = e.hom.hom ∘ ⇑c :=
      funext fun g => cocycles₁congr_apply e c g
    rw [hcomp]
    exact hlc.comp _
  · intro q hq A' hA'
    obtain ⟨m, hm⟩ := hur q hq A' hA'
    refine ⟨e.hom.hom m, fun g hg => ?_⟩
    rw [cocycles₁congr_apply, hm g hg, map_sub, Rep.hom_comm_apply]

private theorem globalClause_congr (S : Finset Nat.Primes) {p : ℕ} [Fact p.Prime]
    {A B : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)} (e : A ≅ B) (x : H1 A) :
    GlobalClause S A x ↔ GlobalClause S B (H1congr e x) := by
  refine ⟨globalClause_map S e x, fun h => ?_⟩
  have h' := globalClause_map S e.symm (H1congr e x) h
  rwa [H1congr_symm_apply_apply] at h'

private theorem continuityClause_map {k H : Type} [Field k] [Group H]
    (r : H →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) {A B : Rep k H} (e : A ≅ B) (x : H1 A)
    (hx : ContinuityClause r A x) : ContinuityClause r B (H1congr e x) := by
  obtain ⟨c, ⟨F, hF, hlev⟩, hcx⟩ := hx
  refine ⟨cocycles₁congr e c, ⟨F, hF, fun g s hs => ?_⟩, by rw [← hcx, H1congr_H1π]⟩
  show (cocycles₁congr e c : H → B) (g * s) = (cocycles₁congr e c : H → B) g
  rw [cocycles₁congr_apply, cocycles₁congr_apply]
  exact congrArg e.hom.hom (hlev g s hs)

private theorem continuityClause_congr {k H : Type} [Field k] [Group H]
    (r : H →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) {A B : Rep k H} (e : A ≅ B) (x : H1 A) :
    ContinuityClause r A x ↔ ContinuityClause r B (H1congr e x) := by
  refine ⟨continuityClause_map r e x, fun h => ?_⟩
  have h' := continuityClause_map r e.symm (H1congr e x) h
  rwa [H1congr_symm_apply_apply] at h'

private theorem unramifiedClause_map {k H : Type} [Field k] [Group H]
    (r : H →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (I : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) {A B : Rep k H} (e : A ≅ B) (x : H1 A)
    (hx : UnramifiedClause r I A x) : UnramifiedClause r I B (H1congr e x) := by
  obtain ⟨c, ⟨F, hF, hlev⟩, ⟨m, hm⟩, hcx⟩ := hx
  refine ⟨cocycles₁congr e c, ⟨F, hF, fun g s hs => ?_⟩, ⟨e.hom.hom m, fun s hs => ?_⟩,
    by rw [← hcx, H1congr_H1π]⟩
  · show (cocycles₁congr e c : H → B) (g * s) = (cocycles₁congr e c : H → B) g
    rw [cocycles₁congr_apply, cocycles₁congr_apply]
    exact congrArg e.hom.hom (hlev g s hs)
  · show (cocycles₁congr e c : H → B) s = B.ρ s (e.hom.hom m) - e.hom.hom m
    rw [cocycles₁congr_apply, ← Rep.hom_comm_apply, ← map_sub]
    exact congrArg e.hom.hom (hm s hs)

private theorem unramifiedClause_congr {k H : Type} [Field k] [Group H]
    (r : H →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (I : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) {A B : Rep k H} (e : A ≅ B) (x : H1 A) :
    UnramifiedClause r I A x ↔ UnramifiedClause r I B (H1congr e x) := by
  refine ⟨unramifiedClause_map r I e x, fun h => ?_⟩
  have h' := unramifiedClause_map r I e.symm (H1congr e x) h
  rwa [H1congr_symm_apply_apply] at h'

private theorem map_comap_H1congr {k Γ : Type} [Field k] [Group Γ] {A B : Rep k Γ} (e : A ≅ B)
    (U : Submodule k (H1 B)) :
    (U.comap (H1congr e).toLinearMap).map (H1congr e).toLinearMap = U :=
  Submodule.map_comap_eq_of_surjective (H1congr e).surjective U

private theorem condCongr_comap {k Γ : Type} [Field k] [Group Γ] {ι : Type} {Γv : ι → Type}
    [∀ v, Group (Γv v)] (loc : ∀ v, Γv v →* Γ) {A B : Rep k Γ} (e : A ≅ B)
    (L : ∀ v, Submodule k (H1 (Rep.res (loc v) B))) :
    condCongr loc e (fun v => (L v).comap (H1congr ((Rep.resFunctor (loc v)).mapIso e)).toLinearMap) = L := by
  funext v
  exact map_comap_H1congr _ (L v)

private theorem nonempty_dualTwist_dualTwist_iso' {p : ℕ} [Fact p.Prime] {Γ : Type} [Group Γ]
    (χ : Γ →* (ZMod p)ˣ) (M : Rep (ZMod p) Γ) [FiniteDimensional (ZMod p) M] :
    Nonempty ((M.dualTwist χ).dualTwist χ ≅ M) :=
  Rep.nonempty_dualTwist_dualTwist_iso χ M

end Transport

namespace GreenbergWilesMenu

section Glue

variable {p : ℕ} [Fact p.Prime]

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

end Glue

section Local

variable {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes)
  (X : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))

private theorem smooth_res
    (hsm : ∀ m : X, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s ∈ F.fixingSubgroup, X.ρ s m = m) (q : ↥S) :
    ∀ m : Rep.res (extArithLoc S (Sum.inr q)) X,
      ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
        ∀ s, primeLocalToGlobal q.1 s ∈ F.fixingSubgroup →
          (Rep.res (extArithLoc S (Sum.inr q)) X).ρ s m = m := by
  intro m
  obtain ⟨F, hFD, hF⟩ := hsm m
  exact ⟨F, hFD, fun s hs => hF _ hs⟩

private theorem finiteDimensional_continuousH1_res [FiniteDimensional (ZMod p) X]
    (hsm : ∀ m : X, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s ∈ F.fixingSubgroup, X.ρ s m = m) (q : ↥S) :
    FiniteDimensional (ZMod p)
      (continuousH1 (extArithLoc S (Sum.inr q)) (Rep.res (extArithLoc S (Sum.inr q)) X)) := by
  have hT : ∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧
      F₀.fixingSubgroup.comap (primeLocalToGlobal q.1) ≤ (⊤ : Subgroup (primeLocalGaloisGroup q.1)) :=
    ⟨⊥, inferInstance, le_top⟩
  haveI : FiniteDimensional (ZMod p)
      (Rep.res (⊤ : Subgroup (primeLocalGaloisGroup q.1)).subtype
        (Rep.res (extArithLoc S (Sum.inr q)) X)) :=
    inferInstanceAs (FiniteDimensional (ZMod p) X)
  have hsmN : ∀ n : (Rep.res (⊤ : Subgroup (primeLocalGaloisGroup q.1)).subtype
        (Rep.res (extArithLoc S (Sum.inr q)) X)),
      ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
        ∀ s : (⊤ : Subgroup (primeLocalGaloisGroup q.1)),
          ((primeLocalToGlobal q.1).comp (⊤ : Subgroup _).subtype) s ∈ F.fixingSubgroup →
            (Rep.res (⊤ : Subgroup (primeLocalGaloisGroup q.1)).subtype
              (Rep.res (extArithLoc S (Sum.inr q)) X)).ρ s n = n := by
    intro n
    obtain ⟨F, hFD, hF⟩ := hsm n
    exact ⟨F, hFD, fun s hs => hF _ hs⟩
  have h9 := groupCohomology.finiteDimensional_continuousH1_of_isOpen_of_primeLocal (p := p) q.1 ⊤ hT
    (Rep.res (⊤ : Subgroup (primeLocalGaloisGroup q.1)).subtype (Rep.res (extArithLoc S (Sum.inr q)) X))
    hsmN
  exact finiteDimensional_continuousH1_of_top (primeLocalToGlobal q.1)
    (Rep.res (extArithLoc S (Sum.inr q)) X) h9

private theorem finiteDimensional_of_forall_mem_imp [FiniteDimensional (ZMod p) X]
    (hsm : ∀ m : X, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s ∈ F.fixingSubgroup, X.ρ s m = m) (q : ↥S)
    (N : Submodule (ZMod p) (H1 (Rep.res (extArithLoc S (Sum.inr q)) X)))
    (hN : ∀ x ∈ N, ∃ c : cocycles₁ (Rep.res (extArithLoc S (Sum.inr q)) X),
      (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
        ∀ g s, extArithLoc S (Sum.inr q) s ∈ F.fixingSubgroup → c.val (g * s) = c.val g) ∧
      (H1π _).hom c = x) :
    FiniteDimensional (ZMod p) N := by
  haveI := finiteDimensional_continuousH1_res S X hsm q
  refine Submodule.finiteDimensional_of_le (S₂ := continuousH1 (extArithLoc S (Sum.inr q))
    (Rep.res (extArithLoc S (Sum.inr q)) X)) ?_
  intro x hx
  obtain ⟨c, hc, rfl⟩ := hN x hx
  exact H1π_mem_continuousH1 _ _ hc

private theorem finrank_continuousH1_res [FiniteDimensional (ZMod p) X]
    (hsm : ∀ m : X, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s ∈ F.fixingSubgroup, X.ρ s m = m) (q : ↥S) :
    finrank (ZMod p)
        (continuousH1 (extArithLoc S (Sum.inr q)) (Rep.res (extArithLoc S (Sum.inr q)) X))
      = finrank (ZMod p) (Rep.res (extArithLoc S (Sum.inr q)) X).ρ.invariants
        + finrank (ZMod p) ((Rep.res (extArithLoc S (Sum.inr q)) X).dualTwist
            ((cycloChar p).comp (extArithLoc S (Sum.inr q)))).ρ.invariants
        + (if ((q : Nat.Primes) : ℕ) = p then finrank (ZMod p) X else 0) := by
  haveI := finiteDimensional_continuousH1_res S X hsm q
  have hadm := fun x => (mem_continuousH1_iff (extArithLoc S (Sum.inr q))
    (Rep.res (extArithLoc S (Sum.inr q)) X) x)
  by_cases hqp : ((q : Nat.Primes) : ℕ) = p
  · rw [if_pos hqp]
    exact @groupCohomology.finrank_finiteQuotientH1_eq_invariants_add_dualTwist_add_finrank_of_primeLocal
      p _ q.1 hqp (Rep.res (extArithLoc S (Sum.inr q)) X) (inferInstanceAs (FiniteDimensional (ZMod p) X))
      (smooth_res S X hsm q) _ this hadm
  · rw [if_neg hqp, Nat.add_zero]
    exact @groupCohomology.finrank_finiteQuotientH1_eq_invariants_add_dualTwist_of_primeLocal_ne
      p _ q.1 hqp (Rep.res (extArithLoc S (Sum.inr q)) X) (inferInstanceAs (FiniteDimensional (ZMod p) X))
      (smooth_res S X hsm q) _ this hadm

end Local

section Balance

variable {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
  (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) [FiniteDimensional (ZMod p) M]
  (T₁ T₀ : Finset ↥S)
  (L : ∀ v, Submodule (ZMod p) (H1 (Rep.res (extArithLoc S v) M)))
  (L' : ∀ v, Submodule (ZMod p) (H1 (Rep.res (extArithLoc S v) (M.dualTwist (cycloChar p)))))

private theorem finiteDimensional_dualTwist :
    FiniteDimensional (ZMod p) (M.dualTwist (cycloChar p)) :=
  inferInstanceAs (FiniteDimensional (ZMod p) (Module.Dual (ZMod p) M))

omit [FiniteDimensional (ZMod p) M] in
private theorem finrank_dualTwist : finrank (ZMod p) (M.dualTwist (cycloChar p)) = finrank (ZMod p) M :=
  Subspace.dual_finrank_eq

private theorem finrank_invariants_dualTwist_dualTwist_res (q : ↥S) :
    finrank (ZMod p) ((Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p))).dualTwist
        ((cycloChar p).comp (extArithLoc S (Sum.inr q)))).ρ.invariants
      = finrank (ZMod p) (Rep.res (extArithLoc S (Sum.inr q)) M).ρ.invariants := by
  haveI := finiteDimensional_dualTwist M
  rw [← Rep.finrank_invariants_res_dualTwist_eq (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p))]
  obtain ⟨e⟩ := Rep.nonempty_dualTwist_dualTwist_iso (cycloChar p) M
  exact finrank_invariants_congr ((Rep.resFunctor (extArithLoc S (Sum.inr q))).mapIso e)

include hpS in

private theorem place_balance
    (hsm : ∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s ∈ F.fixingSubgroup, M.ρ s m = m)
    (hpT : (⟨pPrime p, hpS⟩ : ↥S) ∈ T₁ ∪ T₀)
    (hL₁ : ∀ q ∈ T₁, ∀ x, x ∈ L (Sum.inr q) ↔
      ∃ c : cocycles₁ (Rep.res (extArithLoc S (Sum.inr q)) M),
        (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
          ∀ g s, extArithLoc S (Sum.inr q) s ∈ F.fixingSubgroup → c.val (g * s) = c.val g) ∧
        H1π _ c = x)
    (hL'₁ : ∀ q ∈ T₁, L' (Sum.inr q) = ⊥)
    (hL₀ : ∀ q ∈ T₀, L (Sum.inr q) = ⊥)
    (hL'₀ : ∀ q ∈ T₀, ∀ x, x ∈ L' (Sum.inr q) ↔
      ∃ c : cocycles₁ (Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p))),
        (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
          ∀ g s, extArithLoc S (Sum.inr q) s ∈ F.fixingSubgroup → c.val (g * s) = c.val g) ∧
        H1π _ c = x)
    (hLur : ∀ q : ↥S, q ∉ T₁ ∪ T₀ → ∀ x, x ∈ L (Sum.inr q) ↔
      ∃ c : cocycles₁ (Rep.res (extArithLoc S (Sum.inr q)) M),
        (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
          ∀ g s, extArithLoc S (Sum.inr q) s ∈ F.fixingSubgroup → c.val (g * s) = c.val g) ∧
        (∃ m : M, ∀ s, extArithLoc S (Sum.inr q) s ∈ (primeLocalPlace q.1).inertiaSubgroupIn ℚ →
          c.val s = (Rep.res (extArithLoc S (Sum.inr q)) M).ρ s m - m) ∧
        H1π _ c = x)
    (hL'ur : ∀ q : ↥S, q ∉ T₁ ∪ T₀ → ∀ x, x ∈ L' (Sum.inr q) ↔
      ∃ c : cocycles₁ (Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p))),
        (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
          ∀ g s, extArithLoc S (Sum.inr q) s ∈ F.fixingSubgroup → c.val (g * s) = c.val g) ∧
        (∃ m : M.dualTwist (cycloChar p),
          ∀ s, extArithLoc S (Sum.inr q) s ∈ (primeLocalPlace q.1).inertiaSubgroupIn ℚ →
          c.val s = (Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p))).ρ s m - m) ∧
        H1π _ c = x)
    (q : ↥S) :
    finrank (ZMod p) (L (Sum.inr q)) + finrank (ZMod p) (L' (Sum.inr q))
      = finrank (ZMod p) (Rep.res (extArithLoc S (Sum.inr q)) M).ρ.invariants
        + finrank (ZMod p) (Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p))).ρ.invariants
        + (if ((q : Nat.Primes) : ℕ) = p then finrank (ZMod p) M else 0) := by
  haveI := finiteDimensional_dualTwist M
  have hsm' := Rep.dualTwist_cycloChar_smooth M hsm
  by_cases h₁ : q ∈ T₁
  ·
    have hLq : L (Sum.inr q) = continuousH1 (extArithLoc S (Sum.inr q)) (Rep.res (extArithLoc S (Sum.inr q)) M) :=
      eq_continuousH1_of_forall_mem_iff _ _ _ (hL₁ q h₁)
    rw [hL'₁ q h₁, finrank_bot, Nat.add_zero, hLq, finrank_continuousH1_res S M hsm q,
      ← Rep.finrank_invariants_res_dualTwist_eq (extArithLoc S (Sum.inr q)) M]
  by_cases h₀ : q ∈ T₀
  ·
    have hL'q : L' (Sum.inr q) = continuousH1 (extArithLoc S (Sum.inr q))
        (Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p))) :=
      eq_continuousH1_of_forall_mem_iff _ _ _ (hL'₀ q h₀)
    rw [hL₀ q h₀, finrank_bot, Nat.zero_add, hL'q, finrank_continuousH1_res S (M.dualTwist (cycloChar p)) hsm' q,
      finrank_invariants_dualTwist_dualTwist_res S M q, finrank_dualTwist M]
    omega
  ·
    have hq : q ∉ T₁ ∪ T₀ := by
      intro h
      rcases Finset.mem_union.mp h with h | h
      · exact h₁ h
      · exact h₀ h
    have hqp : ((q : Nat.Primes) : ℕ) ≠ p := by
      intro hqp
      apply hq
      have : q = (⟨pPrime p, hpS⟩ : ↥S) := Subtype.ext (Subtype.ext hqp)
      rw [this]
      exact hpT
    rw [if_neg hqp, Nat.add_zero]
    haveI hFL : FiniteDimensional (ZMod p) (L (Sum.inr q)) :=
      finiteDimensional_of_forall_mem_imp S M hsm q _ (fun x hx => by
        obtain ⟨c, hF, -, hc⟩ := (hLur q hq x).1 hx
        exact ⟨c, hF, hc⟩)
    haveI hFL' : FiniteDimensional (ZMod p) (L' (Sum.inr q)) :=
      finiteDimensional_of_forall_mem_imp S (M.dualTwist (cycloChar p)) hsm' q _ (fun x hx => by
        obtain ⟨c, hF, -, hc⟩ := (hL'ur q hq x).1 hx
        exact ⟨c, hF, hc⟩)
    have e₁ := @ExtCitation.finrank_unramifiedContinuousClasses_eq_finrank_invariants p _ q.1
      (Rep.res (extArithLoc S (Sum.inr q)) M) (inferInstanceAs (FiniteDimensional (ZMod p) M))
      (smooth_res S M hsm q) (L (Sum.inr q)) hFL (hLur q hq)
    have e₂ := @ExtCitation.finrank_unramifiedContinuousClasses_eq_finrank_invariants p _ q.1
      (Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p)))
      (inferInstanceAs (FiniteDimensional (ZMod p) (Module.Dual (ZMod p) M)))
      (smooth_res S (M.dualTwist (cycloChar p)) hsm' q) (L' (Sum.inr q)) hFL' (hL'ur q hq)
    have e₁' : finrank (ZMod p) (L (Sum.inr q))
        = finrank (ZMod p) (Rep.res (extArithLoc S (Sum.inr q)) M).ρ.invariants := e₁
    have e₂' : finrank (ZMod p) (L' (Sum.inr q))
        = finrank (ZMod p) (Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p))).ρ.invariants := e₂
    rw [e₁', e₂']

include hp2 in

private theorem arch_balance (u : Unit) :
    finrank (ZMod p) (L (Sum.inl u)) = 0 ∧ finrank (ZMod p) (L' (Sum.inl u)) = 0 := by
  haveI := finiteDimensional_dualTwist M
  exact ⟨groupCohomology.finrank_submodule_res_extArithLoc_archSlot_eq_zero hp2 S M u (L (Sum.inl u)),
    groupCohomology.finrank_submodule_res_extArithLoc_archSlot_eq_zero hp2 S (M.dualTwist (cycloChar p)) u
      (L' (Sum.inl u))⟩

omit [FiniteDimensional (ZMod p) M] in
private theorem finrank_H1_arch_eq_zero
    (hinf : Subsingleton (H1 (Rep.res (extArithLoc S (Sum.inl ())) M))) :
    finrank (ZMod p) (H1 (Rep.res (extArithLoc S (Sum.inl ())) M)) = 0 := by
  haveI := hinf
  exact Module.finrank_zero_of_subsingleton

private theorem arch_h0_balance (hinf : Subsingleton (H1 (Rep.res (extArithLoc S (Sum.inl ())) M))) :
    finrank (ZMod p) (Rep.res (extArithLoc S (Sum.inl ())) M).ρ.invariants
        + finrank (ZMod p) (Rep.res (extArithLoc S (Sum.inl ())) (M.dualTwist (cycloChar p))).ρ.invariants
      = finrank (ZMod p) M := by
  have hEP := groupCohomology.finrank_invariants_archimedean_add_dualTwist_add_H1_eq S M
  have h1 := finrank_H1_arch_eq_zero S M hinf
  have h2 : finrank (ZMod p)
      (continuousH2 (extArithLoc S (Sum.inl ())) (Rep.res (extArithLoc S (Sum.inl ())) M)) = 0 :=
    TWNum.finrank_continuousH2_extArithLoc_inl_eq_zero S M hinf
  omega

private theorem sum_index_eq (f : extArithIndex S → ℕ) :
    ∑ v, f v = f (Sum.inl ()) + ∑ q : ↥S, f (Sum.inr q) := by
  have h : (∑ v, f v) = ∑ v : Unit ⊕ ↥S, f v := rfl
  rw [h, Fintype.sum_sum_type, Fintype.sum_unique]

omit [FiniteDimensional (ZMod p) M] in
include hpS in

private theorem sum_ite_eq_finrank :
    (∑ q : ↥S, (if ((q : Nat.Primes) : ℕ) = p then finrank (ZMod p) M else 0)) = finrank (ZMod p) M := by
  have h : ∀ q : ↥S, (if ((q : Nat.Primes) : ℕ) = p then finrank (ZMod p) M else 0)
      = if q = (⟨pPrime p, hpS⟩ : ↥S) then finrank (ZMod p) M else 0 := by
    intro q
    by_cases hq : ((q : Nat.Primes) : ℕ) = p
    · have hq' : q = (⟨pPrime p, hpS⟩ : ↥S) := Subtype.ext (Subtype.ext hq)
      rw [if_pos hq, if_pos hq']
    · rw [if_neg hq, if_neg]
      rintro rfl
      exact hq rfl
  simp only [h, Finset.sum_ite_eq', Finset.mem_univ, if_true]

include hp2 hpS in

private theorem sum_balance
    (hsm : ∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s ∈ F.fixingSubgroup, M.ρ s m = m)
    (hpT : (⟨pPrime p, hpS⟩ : ↥S) ∈ T₁ ∪ T₀)
    (hL₁ : ∀ q ∈ T₁, ∀ x, x ∈ L (Sum.inr q) ↔
      ∃ c : cocycles₁ (Rep.res (extArithLoc S (Sum.inr q)) M),
        (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
          ∀ g s, extArithLoc S (Sum.inr q) s ∈ F.fixingSubgroup → c.val (g * s) = c.val g) ∧
        H1π _ c = x)
    (hL'₁ : ∀ q ∈ T₁, L' (Sum.inr q) = ⊥)
    (hL₀ : ∀ q ∈ T₀, L (Sum.inr q) = ⊥)
    (hL'₀ : ∀ q ∈ T₀, ∀ x, x ∈ L' (Sum.inr q) ↔
      ∃ c : cocycles₁ (Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p))),
        (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
          ∀ g s, extArithLoc S (Sum.inr q) s ∈ F.fixingSubgroup → c.val (g * s) = c.val g) ∧
        H1π _ c = x)
    (hLur : ∀ q : ↥S, q ∉ T₁ ∪ T₀ → ∀ x, x ∈ L (Sum.inr q) ↔
      ∃ c : cocycles₁ (Rep.res (extArithLoc S (Sum.inr q)) M),
        (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
          ∀ g s, extArithLoc S (Sum.inr q) s ∈ F.fixingSubgroup → c.val (g * s) = c.val g) ∧
        (∃ m : M, ∀ s, extArithLoc S (Sum.inr q) s ∈ (primeLocalPlace q.1).inertiaSubgroupIn ℚ →
          c.val s = (Rep.res (extArithLoc S (Sum.inr q)) M).ρ s m - m) ∧
        H1π _ c = x)
    (hL'ur : ∀ q : ↥S, q ∉ T₁ ∪ T₀ → ∀ x, x ∈ L' (Sum.inr q) ↔
      ∃ c : cocycles₁ (Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p))),
        (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
          ∀ g s, extArithLoc S (Sum.inr q) s ∈ F.fixingSubgroup → c.val (g * s) = c.val g) ∧
        (∃ m : M.dualTwist (cycloChar p),
          ∀ s, extArithLoc S (Sum.inr q) s ∈ (primeLocalPlace q.1).inertiaSubgroupIn ℚ →
          c.val s = (Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p))).ρ s m - m) ∧
        H1π _ c = x)
    (hinf : Subsingleton (H1 (Rep.res (extArithLoc S (Sum.inl ())) M))) :
    (∑ v, finrank (ZMod p) (L v)) + ∑ v, finrank (ZMod p) (L' v)
      = (∑ v, finrank (ZMod p) (Rep.res (extArithLoc S v) M).ρ.invariants)
        + ∑ v, finrank (ZMod p) (Rep.res (extArithLoc S v) (M.dualTwist (cycloChar p))).ρ.invariants := by
  rw [sum_index_eq S (fun v => finrank (ZMod p) (L v)), sum_index_eq S (fun v => finrank (ZMod p) (L' v)),
    sum_index_eq S (fun v => finrank (ZMod p) (Rep.res (extArithLoc S v) M).ρ.invariants),
    sum_index_eq S (fun v => finrank (ZMod p)
      (Rep.res (extArithLoc S v) (M.dualTwist (cycloChar p))).ρ.invariants)]
  obtain ⟨hA, hA'⟩ := arch_balance hp2 S M L L' ()
  have hR2 := arch_h0_balance S M hinf
  have hS : (∑ q : ↥S, finrank (ZMod p) (L (Sum.inr q))) + ∑ q : ↥S, finrank (ZMod p) (L' (Sum.inr q))
      = (∑ q : ↥S, finrank (ZMod p) (Rep.res (extArithLoc S (Sum.inr q)) M).ρ.invariants)
        + (∑ q : ↥S, finrank (ZMod p)
            (Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p))).ρ.invariants)
        + finrank (ZMod p) M := by
    rw [← Finset.sum_add_distrib, ← sum_ite_eq_finrank S hpS M, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun q _ =>
      place_balance S hpS M T₁ T₀ L L' hsm hpT hL₁ hL'₁ hL₀ hL'₀ hLur hL'ur q
  omega

end Balance

private theorem assemble {a b c d e f g h : ℕ} (hA : a + b + c ≤ d + e + f) (hB : d + e + g ≤ a + b + h)
    (hE : f + h = c + g) : a + b + c = d + e + f := by
  omega

end GreenbergWilesMenu

section UrPlaces

private noncomputable def resDualTwistIso {k Γ H : Type} [Field k] [Group Γ] [Group H] (r : H →* Γ)
    (M : Rep k Γ) (χ : Γ →* kˣ) :
    Rep.res r (M.dualTwist χ) ≅ (Rep.res r M).dualTwist (χ.comp r) :=
  Rep.mkIso (Representation.Equiv.mk (ρ := (Rep.res r (M.dualTwist χ)).ρ)
    (σ := ((Rep.res r M).dualTwist (χ.comp r)).ρ) (LinearEquiv.refl k (Module.Dual k M)) fun s =>
      LinearMap.ext fun f => by
        show (χ (r s) : k) • (f ∘ₗ M.ρ (r s)⁻¹) = (χ (r s) : k) • (f ∘ₗ M.ρ (r s⁻¹))
        rw [map_inv r s])

private theorem finrank_invariants_dualTwist_res_dualTwist {p : ℕ} [Fact p.Prime] {Γ H : Type}
    [Group Γ] [Group H] (r : H →* Γ) (M : Rep (ZMod p) Γ) [FiniteDimensional (ZMod p) M]
    (χ : Γ →* (ZMod p)ˣ) :
    finrank (ZMod p) ((Rep.res r (M.dualTwist χ)).dualTwist (χ.comp r)).ρ.invariants
      = finrank (ZMod p) (Rep.res r M).ρ.invariants := by
  obtain ⟨e⟩ := nonempty_dualTwist_dualTwist_iso' χ M
  exact finrank_invariants_congr
    ((resDualTwistIso r (M.dualTwist χ) χ).symm.trans ((Rep.resFunctor r).mapIso e))

end UrPlaces

private theorem subsingleton_H1_archSlot
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (S : Finset Nat.Primes)
    (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) [FiniteDimensional (ZMod p) M] :
    Subsingleton (H1 (Rep.res (extArithLoc S (Sum.inl ())) M)) := by
  have h0 : ∀ x : H1 (Rep.res (extArithLoc S (Sum.inl ())) M), x = 0 := by
    intro x
    by_contra hx
    have h := finrank_submodule_res_extArithLoc_archSlot_eq_zero hp2 S M () (Submodule.span (ZMod p) {x})
    rw [finrank_span_singleton hx] at h
    exact one_ne_zero h
  exact ⟨fun x y => (h0 x).trans (h0 y).symm⟩

private theorem exists_localDualityPackage
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes)
    (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) [FiniteDimensional (ZMod p) M]
    (hsm : ∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s ∈ F.fixingSubgroup, M.ρ s m = m) (q : ↥S) :
    ∃ (inv : continuousH2 (extArithLoc S (Sum.inr q))
          (ofChar (k := ZMod p) ((cycloChar p).comp (extArithLoc S (Sum.inr q)))) →ₗ[ZMod p] ZMod p)
      (θ : continuousH1 (extArithLoc S (Sum.inr q)) (Rep.res (extArithLoc S (Sum.inr q)) M) →ₗ[ZMod p]
        Module.Dual (ZMod p) (continuousH1 (extArithLoc S (Sum.inr q))
          (Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p))))),
      Function.Bijective inv ∧
      IsTheta1 (extArithLoc S (Sum.inr q))
        (Module.Dual.eval (ZMod p) M :
          Rep.res (extArithLoc S (Sum.inr q)) M →ₗ[ZMod p]
            Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p)) →ₗ[ZMod p]
              ofChar (k := ZMod p) ((cycloChar p).comp (extArithLoc S (Sum.inr q)))) inv θ ∧
      Function.Bijective θ :=
  groupCohomology.exists_localDualityPackage_res_dualTwist_extArithLoc S M hsm q

private theorem exists_pairing_agreeing_on_continuous
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes)
    (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (v : extArithIndex S)
    (θ : continuousH1 (extArithLoc S v) (Rep.res (extArithLoc S v) M) →ₗ[ZMod p]
      Module.Dual (ZMod p) (continuousH1 (extArithLoc S v)
        (Rep.res (extArithLoc S v) (M.dualTwist (cycloChar p))))) :
    ∃ P : H1 (Rep.res (extArithLoc S v) M) →ₗ[ZMod p]
        H1 (Rep.res (extArithLoc S v) (M.dualTwist (cycloChar p))) →ₗ[ZMod p] ZMod p,
      ∀ (x : continuousH1 (extArithLoc S v) (Rep.res (extArithLoc S v) M))
        (y : continuousH1 (extArithLoc S v) (Rep.res (extArithLoc S v) (M.dualTwist (cycloChar p)))),
        P (x : H1 _) (y : H1 _) = θ x y := by
  obtain ⟨Θ, hΘ⟩ := LinearMap.exists_extend θ
  obtain ⟨g, hg⟩ := LinearMap.exists_extend (LinearMap.id : continuousH1 (extArithLoc S v)
    (Rep.res (extArithLoc S v) (M.dualTwist (cycloChar p))) →ₗ[ZMod p] _)
  refine ⟨(LinearMap.lcomp (ZMod p) (ZMod p) g).comp Θ, fun x y => ?_⟩
  have hx : Θ (x : H1 _) = θ x := LinearMap.congr_fun hΘ x
  have hy : g (y : H1 _) = y := LinearMap.congr_fun hg y
  simp only [LinearMap.comp_apply, LinearMap.lcomp_apply, hx, hy]

private theorem dualTwist_cycloChar_smooth'
    {p : ℕ} [Fact p.Prime] (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    [FiniteDimensional (ZMod p) M]
    (hsm : ∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s ∈ F.fixingSubgroup, M.ρ s m = m) :
    ∀ f : M.dualTwist (cycloChar p), ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s ∈ F.fixingSubgroup, (M.dualTwist (cycloChar p)).ρ s f = f :=
  Rep.dualTwist_cycloChar_smooth M hsm

private theorem dualTwist_cycloChar_unramified_outside
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (hMur : ∀ q : Nat.Primes, q ∉ S → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
      A.LiesOverPrime (q : ℕ) → ∀ g ∈ A.inertiaSubgroupIn ℚ, M.ρ g = 1) :
    ∀ q : Nat.Primes, q ∉ S → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
      A.LiesOverPrime (q : ℕ) → ∀ g ∈ A.inertiaSubgroupIn ℚ, (M.dualTwist (cycloChar p)).ρ g = 1 :=
  Rep.dualTwist_cycloChar_unramifiedOutside S hpS M hMur

private theorem mem_unramifiedMenu_of_orthogonal
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) [FiniteDimensional (ZMod p) M]
    (hsm : ∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s ∈ F.fixingSubgroup, M.ρ s m = m)
    (q : ↥S) (hq : q ≠ ⟨pPrime p, hpS⟩)
    (inv : continuousH2 (extArithLoc S (Sum.inr q))
      (ofChar (k := ZMod p) ((cycloChar p).comp (extArithLoc S (Sum.inr q)))) →ₗ[ZMod p] ZMod p)
    (θ : continuousH1 (extArithLoc S (Sum.inr q)) (Rep.res (extArithLoc S (Sum.inr q)) M) →ₗ[ZMod p]
      Module.Dual (ZMod p) (continuousH1 (extArithLoc S (Sum.inr q))
        (Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p)))))
    (hθ : IsTheta1 (extArithLoc S (Sum.inr q))
      (Module.Dual.eval (ZMod p) M :
        Rep.res (extArithLoc S (Sum.inr q)) M →ₗ[ZMod p]
          Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p)) →ₗ[ZMod p]
            ofChar (k := ZMod p) ((cycloChar p).comp (extArithLoc S (Sum.inr q)))) inv θ)
    (hbijθ : Function.Bijective θ)
    (Lq : Submodule (ZMod p) (H1 (Rep.res (extArithLoc S (Sum.inr q)) M)))
    (hLq : ∀ x, x ∈ Lq ↔
      ∃ c : cocycles₁ (Rep.res (extArithLoc S (Sum.inr q)) M),
        (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
          ∀ g s, extArithLoc S (Sum.inr q) s ∈ F.fixingSubgroup → c.val (g * s) = c.val g) ∧
        (∃ m : M, ∀ s, extArithLoc S (Sum.inr q) s ∈ (primeLocalPlace q.1).inertiaSubgroupIn ℚ →
          c.val s = (Rep.res (extArithLoc S (Sum.inr q)) M).ρ s m - m) ∧
        H1π _ c = x)
    (L'q : Submodule (ZMod p) (H1 (Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p)))))
    (hL'q : ∀ x, x ∈ L'q ↔
      ∃ c : cocycles₁ (Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p))),
        (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
          ∀ g s, extArithLoc S (Sum.inr q) s ∈ F.fixingSubgroup → c.val (g * s) = c.val g) ∧
        (∃ m : M.dualTwist (cycloChar p),
          ∀ s, extArithLoc S (Sum.inr q) s ∈ (primeLocalPlace q.1).inertiaSubgroupIn ℚ →
          c.val s = (Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p))).ρ s m - m) ∧
        H1π _ c = x)
    (y : continuousH1 (extArithLoc S (Sum.inr q))
      (Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p))))
    (hy : ∀ x : H1 (Rep.res (extArithLoc S (Sum.inr q)) M), x ∈ Lq →
      ∀ hxc : x ∈ continuousH1 (extArithLoc S (Sum.inr q)) (Rep.res (extArithLoc S (Sum.inr q)) M),
        θ ⟨x, hxc⟩ y = 0) :
    (y : H1 _) ∈ L'q := by
  have hne : ((q : Nat.Primes) : ℕ) ≠ p := fun h => hq (Subtype.ext (Subtype.ext h))
  have hsm' := Rep.dualTwist_cycloChar_smooth M hsm
  haveI hfdM : FiniteDimensional (ZMod p) (continuousH1 (extArithLoc S (Sum.inr q)) (Rep.res (extArithLoc S (Sum.inr q)) M)) :=
    GreenbergWilesMenu.finiteDimensional_continuousH1_res S M hsm q
  haveI hfdD : FiniteDimensional (ZMod p) (continuousH1 (extArithLoc S (Sum.inr q)) (Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p)))) :=
    GreenbergWilesMenu.finiteDimensional_continuousH1_res S (M.dualTwist (cycloChar p)) hsm' q

  have hLq_le : Lq ≤ continuousH1 (extArithLoc S (Sum.inr q)) (Rep.res (extArithLoc S (Sum.inr q)) M) := by
    intro x hx
    obtain ⟨c, hlev, -, hcx⟩ := (hLq x).1 hx
    rw [← hcx]
    exact H1π_mem_continuousH1 _ _ hlev
  have hL'q_le : L'q ≤ continuousH1 (extArithLoc S (Sum.inr q)) (Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p))) := by
    intro x hx
    obtain ⟨c, hlev, -, hcx⟩ := (hL'q x).1 hx
    rw [← hcx]
    exact H1π_mem_continuousH1 _ _ hlev
  have hfdLq : FiniteDimensional (ZMod p) Lq :=
    GreenbergWilesMenu.finiteDimensional_of_forall_mem_imp S M hsm q _ (fun x hx => by
      obtain ⟨c, hF, -, hc⟩ := (hLq x).1 hx
      exact ⟨c, hF, hc⟩)
  have hfdL'q : FiniteDimensional (ZMod p) L'q :=
    GreenbergWilesMenu.finiteDimensional_of_forall_mem_imp S (M.dualTwist (cycloChar p)) hsm' q _
      (fun x hx => by
        obtain ⟨c, hF, -, hc⟩ := (hL'q x).1 hx
        exact ⟨c, hF, hc⟩)

  let U : Submodule (ZMod p) (continuousH1 (extArithLoc S (Sum.inr q)) (Rep.res (extArithLoc S (Sum.inr q)) M)) :=
    Lq.comap (Submodule.subtype _)
  let U' : Submodule (ZMod p) (continuousH1 (extArithLoc S (Sum.inr q)) (Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p)))) :=
    L'q.comap (Submodule.subtype _)
  let Ann : Submodule (ZMod p) (continuousH1 (extArithLoc S (Sum.inr q)) (Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p)))) :=
    (U.map θ).dualCoannihilator
  have hmemAnn : ∀ w, w ∈ Ann ↔ ∀ u ∈ U, θ u w = 0 := by
    intro w
    constructor
    · intro h u hu
      exact (Submodule.mem_dualCoannihilator w).1 h _ (Submodule.mem_map_of_mem hu)
    · intro h
      rw [Submodule.mem_dualCoannihilator]
      rintro φ ⟨u, hu, rfl⟩
      exact h u hu

  have hle : U' ≤ Ann := by
    intro w hw
    rw [hmemAnn]
    intro u hu
    exact theta1_apply_eq_zero_of_mem_unramified_of_mem_unramified q.1 M hsm inv θ hθ Lq hLq L'q hL'q u
      (Submodule.mem_comap.1 hu) w (Submodule.mem_comap.1 hw)

  have hA : finrank (ZMod p) (U.map θ) + finrank (ZMod p) Ann
      = finrank (ZMod p) (continuousH1 (extArithLoc S (Sum.inr q)) (Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p)))) :=
    Subspace.finrank_add_finrank_dualCoannihilator_eq (U.map θ)
  have hB : finrank (ZMod p) U = finrank (ZMod p) (U.map θ) :=
    (Submodule.equivMapOfInjective θ hbijθ.1 U).finrank_eq
  have hC : finrank (ZMod p) U = finrank (ZMod p) Lq :=
    (Submodule.comapSubtypeEquivOfLe hLq_le).finrank_eq
  have hC' : finrank (ZMod p) U' = finrank (ZMod p) L'q :=
    (Submodule.comapSubtypeEquivOfLe hL'q_le).finrank_eq
  have hD := @ExtCitation.finrank_unramifiedContinuousClasses_eq_finrank_invariants p _ q.1
    (Rep.res (extArithLoc S (Sum.inr q)) M) (inferInstanceAs (FiniteDimensional (ZMod p) M))
    (GreenbergWilesMenu.smooth_res S M hsm q) Lq hfdLq hLq
  have hD₁ : finrank (ZMod p) Lq = finrank (ZMod p) (Rep.res (extArithLoc S (Sum.inr q)) M).ρ.invariants := hD
  have hD' := @ExtCitation.finrank_unramifiedContinuousClasses_eq_finrank_invariants p _ q.1
    (Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p)))
    (inferInstanceAs (FiniteDimensional (ZMod p) (Module.Dual (ZMod p) M)))
    (GreenbergWilesMenu.smooth_res S (M.dualTwist (cycloChar p)) hsm' q) L'q hfdL'q hL'q
  have hD₂ : finrank (ZMod p) L'q = finrank (ZMod p) (Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p))).ρ.invariants := hD'
  have hE := GreenbergWilesMenu.finrank_continuousH1_res S (M.dualTwist (cycloChar p)) hsm' q
  rw [if_neg hne, Nat.add_zero] at hE
  have hF : finrank (ZMod p) ((Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p))).dualTwist
        ((cycloChar p).comp (extArithLoc S (Sum.inr q)))).ρ.invariants
      = finrank (ZMod p) (Rep.res (extArithLoc S (Sum.inr q)) M).ρ.invariants :=
    finrank_invariants_dualTwist_res_dualTwist (extArithLoc S (Sum.inr q)) M (cycloChar p)

  have hAnn : U' = Ann := Submodule.eq_of_le_of_finrank_eq hle (by omega)
  have hyAnn : y ∈ Ann := by
    rw [hmemAnn]
    intro u hu
    exact hy u.1 (Submodule.mem_comap.1 hu) u.2
  rw [← hAnn] at hyAnn
  exact Submodule.mem_comap.1 hyAnn

private theorem menu_eq_continuousH1_of_mem_iff
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes)
    (N : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (q : ↥S)
    (Lq : Submodule (ZMod p) (H1 (Rep.res (extArithLoc S (Sum.inr q)) N)))
    (h : ∀ x, x ∈ Lq ↔
      ∃ c : cocycles₁ (Rep.res (extArithLoc S (Sum.inr q)) N),
        (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
          ∀ g s, extArithLoc S (Sum.inr q) s ∈ F.fixingSubgroup → c.val (g * s) = c.val g) ∧
        H1π _ c = x) :
    Lq = continuousH1 (extArithLoc S (Sum.inr q)) (Rep.res (extArithLoc S (Sum.inr q)) N) :=
  eq_continuousH1_of_forall_mem_iff _ _ Lq h

private theorem menu_le_continuousH1
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes)
    (N : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (q : ↥S)
    (Lq : Submodule (ZMod p) (H1 (Rep.res (extArithLoc S (Sum.inr q)) N)))
    (h : ∀ x, x ∈ Lq →
      ∃ c : cocycles₁ (Rep.res (extArithLoc S (Sum.inr q)) N),
        (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
          ∀ g s, extArithLoc S (Sum.inr q) s ∈ F.fixingSubgroup → c.val (g * s) = c.val g) ∧
        H1π _ c = x) :
    Lq ≤ continuousH1 (extArithLoc S (Sum.inr q)) (Rep.res (extArithLoc S (Sum.inr q)) N) := by
  intro x hx
  obtain ⟨c, hc, rfl⟩ := h x hx
  exact (mem_continuousH1_iff _ _ _).2 ⟨c, hc, rfl⟩

private theorem selmer_finrank_le
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
    (T₁ T₀ : Finset ↥S) (hT : Disjoint T₁ T₀) (hpT : (⟨pPrime p, hpS⟩ : ↥S) ∈ T₁ ∪ T₀)
    (L : ∀ v, Submodule (ZMod p) (H1 (Rep.res (extArithLoc S v) M)))
    (L' : ∀ v, Submodule (ZMod p) (H1 (Rep.res (extArithLoc S v) (M.dualTwist (cycloChar p)))))

    (hL₁ : ∀ q ∈ T₁, ∀ x, x ∈ L (Sum.inr q) ↔
      ∃ c : cocycles₁ (Rep.res (extArithLoc S (Sum.inr q)) M),
        (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
          ∀ g s, extArithLoc S (Sum.inr q) s ∈ F.fixingSubgroup → c.val (g * s) = c.val g) ∧
        H1π _ c = x)
    (hL'₁ : ∀ q ∈ T₁, L' (Sum.inr q) = ⊥)

    (hL₀ : ∀ q ∈ T₀, L (Sum.inr q) = ⊥)
    (hL'₀ : ∀ q ∈ T₀, ∀ x, x ∈ L' (Sum.inr q) ↔
      ∃ c : cocycles₁ (Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p))),
        (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
          ∀ g s, extArithLoc S (Sum.inr q) s ∈ F.fixingSubgroup → c.val (g * s) = c.val g) ∧
        H1π _ c = x)

    (hLur : ∀ q : ↥S, q ∉ T₁ ∪ T₀ → ∀ x, x ∈ L (Sum.inr q) ↔
      ∃ c : cocycles₁ (Rep.res (extArithLoc S (Sum.inr q)) M),
        (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
          ∀ g s, extArithLoc S (Sum.inr q) s ∈ F.fixingSubgroup → c.val (g * s) = c.val g) ∧
        (∃ m : M, ∀ s, extArithLoc S (Sum.inr q) s ∈ (primeLocalPlace q.1).inertiaSubgroupIn ℚ →
          c.val s = (Rep.res (extArithLoc S (Sum.inr q)) M).ρ s m - m) ∧
        H1π _ c = x)
    (hL'ur : ∀ q : ↥S, q ∉ T₁ ∪ T₀ → ∀ x, x ∈ L' (Sum.inr q) ↔
      ∃ c : cocycles₁ (Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p))),
        (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
          ∀ g s, extArithLoc S (Sum.inr q) s ∈ F.fixingSubgroup → c.val (g * s) = c.val g) ∧
        (∃ m : M.dualTwist (cycloChar p),
          ∀ s, extArithLoc S (Sum.inr q) s ∈ (primeLocalPlace q.1).inertiaSubgroupIn ℚ →
          c.val s = (Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p))).ρ s m - m) ∧
        H1π _ c = x) :
    finrank (ZMod p) (selmerAdm (extArithLoc S) M L adm)
        + finrank (ZMod p) (M.dualTwist (cycloChar p)).ρ.invariants
        + ∑ v, finrank (ZMod p) (Rep.res (extArithLoc S v) M).ρ.invariants
      ≤ finrank (ZMod p) (selmerAdm (extArithLoc S) (M.dualTwist (cycloChar p)) L' adm')
        + finrank (ZMod p) M.ρ.invariants
        + ∑ v, finrank (ZMod p) (L v) := by
  have _ := hT

  obtain ⟨hfin', hcts'⟩ := finiteDimensional_and_locRes_mem_continuousH1_of_adm S
    (M.dualTwist (cycloChar p)) (dualTwist_cycloChar_smooth' M hsm)
    (dualTwist_cycloChar_unramified_outside S hpS M hMur) adm' hadm'
  haveI := hfin'

  haveI hinf : Subsingleton (H1 (Rep.res (extArithLoc S (Sum.inl ())) M)) :=
    subsingleton_H1_archSlot hp2 S M
  haveI hinf' : Subsingleton (H1 (Rep.res (extArithLoc S (Sum.inl ())) (M.dualTwist (cycloChar p)))) :=
    TWNum.subsingleton_H1_extArithLoc_inl_dualTwist S M (cycloChar p) hinf

  choose inv θ hinv hθ hbij using exists_localDualityPackage S M hsm
  choose P hP using fun q : ↥S => exists_pairing_agreeing_on_continuous S M (Sum.inr q) (θ q)
  let pairing : ∀ v : extArithIndex S,
      H1 (Rep.res (extArithLoc S v) M) →ₗ[ZMod p]
        H1 (Rep.res (extArithLoc S v) (M.dualTwist (cycloChar p))) →ₗ[ZMod p] ZMod p :=
    fun v => match v with
      | Sum.inl _ => 0
      | Sum.inr q => P q

  have hLcts : ∀ q : ↥S, L (Sum.inr q) ≤
      continuousH1 (extArithLoc S (Sum.inr q)) (Rep.res (extArithLoc S (Sum.inr q)) M) := by
    intro q
    by_cases h₁ : q ∈ T₁
    · exact (menu_eq_continuousH1_of_mem_iff S M q _ (hL₁ q h₁)).le
    by_cases h₀ : q ∈ T₀
    · rw [hL₀ q h₀]; exact bot_le
    have hq : q ∉ T₁ ∪ T₀ := by simp [h₁, h₀]
    refine menu_le_continuousH1 S M q _ fun x hx => ?_
    obtain ⟨c, hF, -, hc⟩ := (hLur q hq x).1 hx
    exact ⟨c, hF, hc⟩

  have hle := greenbergWilesLeAdm_extArithLoc_of_isTheta1_eval_of_ne_two hp2 S hpS M hsm hMur adm hadm adm' hadm'
    hinf pairing L hLcts inv hinv θ hθ hbij (fun q x y => hP q x y)

  refine le_menu_of_greenbergWilesLeAdm S M (M.dualTwist (cycloChar p)) pairing L L' adm adm'
    hcts' ?_ hle
  intro v y hyc hyd
  cases v with
  | inl u =>
    obtain ⟨⟩ := u
    rw [Subsingleton.elim y 0]
    exact Submodule.zero_mem _
  | inr q =>
    have hdet := (mem_orthogonal_iff_of_agree_on_continuous (extArithLoc S (Sum.inr q)) (P q) (θ q)
      (hP q) (L (Sum.inr q)) (hLcts q) ⟨y, hyc⟩).1 hyd
    by_cases h₁ : q ∈ T₁
    ·
      have hLq := menu_eq_continuousH1_of_mem_iff S M q _ (hL₁ q h₁)
      have hy0 : (⟨y, hyc⟩ : continuousH1 (extArithLoc S (Sum.inr q))
          (Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p)))) = 0 :=
        (theta1_nondegenerate_of_bijective (extArithLoc S (Sum.inr q)) (θ q) (hbij q)).2 ⟨y, hyc⟩
          fun x => hdet x.1 (by rw [hLq]; exact x.2)
      rw [hL'₁ q h₁]
      have : y = 0 := congrArg Subtype.val hy0
      rw [this]
      exact Submodule.zero_mem _
    by_cases h₀ : q ∈ T₀
    ·
      rw [menu_eq_continuousH1_of_mem_iff S (M.dualTwist (cycloChar p)) q _ (hL'₀ q h₀)]
      exact hyc
    have hq : q ∉ T₁ ∪ T₀ := by simp [h₁, h₀]
    have hqp : q ≠ ⟨pPrime p, hpS⟩ := fun h => hq (h ▸ hpT)
    exact mem_unramifiedMenu_of_orthogonal S hpS M hsm q hqp (inv q) (θ q) (hθ q) (hbij q)
      (L (Sum.inr q)) (hLur q hq) (L' (Sum.inr q)) (hL'ur q hq) ⟨y, hyc⟩
      fun x hx _ => hdet x hx

private theorem selmer_finrank_ge
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
    (T₁ T₀ : Finset ↥S) (hT : Disjoint T₁ T₀) (hpT : (⟨pPrime p, hpS⟩ : ↥S) ∈ T₁ ∪ T₀)
    (L : ∀ v, Submodule (ZMod p) (H1 (Rep.res (extArithLoc S v) M)))
    (L' : ∀ v, Submodule (ZMod p) (H1 (Rep.res (extArithLoc S v) (M.dualTwist (cycloChar p)))))

    (hL₁ : ∀ q ∈ T₁, ∀ x, x ∈ L (Sum.inr q) ↔
      ∃ c : cocycles₁ (Rep.res (extArithLoc S (Sum.inr q)) M),
        (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
          ∀ g s, extArithLoc S (Sum.inr q) s ∈ F.fixingSubgroup → c.val (g * s) = c.val g) ∧
        H1π _ c = x)
    (hL'₁ : ∀ q ∈ T₁, L' (Sum.inr q) = ⊥)

    (hL₀ : ∀ q ∈ T₀, L (Sum.inr q) = ⊥)
    (hL'₀ : ∀ q ∈ T₀, ∀ x, x ∈ L' (Sum.inr q) ↔
      ∃ c : cocycles₁ (Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p))),
        (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
          ∀ g s, extArithLoc S (Sum.inr q) s ∈ F.fixingSubgroup → c.val (g * s) = c.val g) ∧
        H1π _ c = x)

    (hLur : ∀ q : ↥S, q ∉ T₁ ∪ T₀ → ∀ x, x ∈ L (Sum.inr q) ↔
      ∃ c : cocycles₁ (Rep.res (extArithLoc S (Sum.inr q)) M),
        (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
          ∀ g s, extArithLoc S (Sum.inr q) s ∈ F.fixingSubgroup → c.val (g * s) = c.val g) ∧
        (∃ m : M, ∀ s, extArithLoc S (Sum.inr q) s ∈ (primeLocalPlace q.1).inertiaSubgroupIn ℚ →
          c.val s = (Rep.res (extArithLoc S (Sum.inr q)) M).ρ s m - m) ∧
        H1π _ c = x)
    (hL'ur : ∀ q : ↥S, q ∉ T₁ ∪ T₀ → ∀ x, x ∈ L' (Sum.inr q) ↔
      ∃ c : cocycles₁ (Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p))),
        (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
          ∀ g s, extArithLoc S (Sum.inr q) s ∈ F.fixingSubgroup → c.val (g * s) = c.val g) ∧
        (∃ m : M.dualTwist (cycloChar p),
          ∀ s, extArithLoc S (Sum.inr q) s ∈ (primeLocalPlace q.1).inertiaSubgroupIn ℚ →
          c.val s = (Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p))).ρ s m - m) ∧
        H1π _ c = x) :
    finrank (ZMod p) (selmerAdm (extArithLoc S) (M.dualTwist (cycloChar p)) L' adm')
        + finrank (ZMod p) M.ρ.invariants
        + ∑ v, finrank (ZMod p) (Rep.res (extArithLoc S v) (M.dualTwist (cycloChar p))).ρ.invariants
      ≤ finrank (ZMod p) (selmerAdm (extArithLoc S) M L adm)
        + finrank (ZMod p) (M.dualTwist (cycloChar p)).ρ.invariants
        + ∑ v, finrank (ZMod p) (L' v) := by
  have _ := hT
  have _ := hL₀
  obtain ⟨e⟩ := nonempty_dualTwist_dualTwist_iso' (cycloChar p) M
  have hsm' := dualTwist_cycloChar_smooth' M hsm
  have hMur' := dualTwist_cycloChar_unramified_outside S hpS M hMur

  have hadm₂ : ∀ x : H1 ((M.dualTwist (cycloChar p)).dualTwist (cycloChar p)),
      x ∈ adm.comap (H1congr e).toLinearMap ↔ GlobalClause S _ x := fun x =>
    (Submodule.mem_comap.trans (hadm (H1congr e x))).trans (globalClause_congr S e x).symm
  obtain ⟨hfin₂, hcts₂⟩ := finiteDimensional_and_locRes_mem_continuousH1_of_adm S
    ((M.dualTwist (cycloChar p)).dualTwist (cycloChar p))
    (dualTwist_cycloChar_smooth' (M.dualTwist (cycloChar p)) hsm')
    (dualTwist_cycloChar_unramified_outside S hpS (M.dualTwist (cycloChar p)) hMur')
    (adm.comap (H1congr e).toLinearMap) hadm₂
  haveI := hfin₂

  haveI hinf : Subsingleton (H1 (Rep.res (extArithLoc S (Sum.inl ())) M)) :=
    subsingleton_H1_archSlot hp2 S M
  haveI hinf' : Subsingleton (H1 (Rep.res (extArithLoc S (Sum.inl ())) (M.dualTwist (cycloChar p)))) :=
    TWNum.subsingleton_H1_extArithLoc_inl_dualTwist S M (cycloChar p) hinf
  haveI hinf'' : Subsingleton (H1 (Rep.res (extArithLoc S (Sum.inl ()))
      ((M.dualTwist (cycloChar p)).dualTwist (cycloChar p)))) :=
    TWNum.subsingleton_H1_extArithLoc_inl_dualTwist S (M.dualTwist (cycloChar p)) (cycloChar p) hinf'

  choose inv θ hinv hθ hbij using exists_localDualityPackage S (M.dualTwist (cycloChar p)) hsm'
  choose P hP using fun q : ↥S =>
    exists_pairing_agreeing_on_continuous S (M.dualTwist (cycloChar p)) (Sum.inr q) (θ q)
  let pairing : ∀ v : extArithIndex S,
      H1 (Rep.res (extArithLoc S v) (M.dualTwist (cycloChar p))) →ₗ[ZMod p]
        H1 (Rep.res (extArithLoc S v) ((M.dualTwist (cycloChar p)).dualTwist (cycloChar p))) →ₗ[ZMod p]
          ZMod p :=
    fun v => match v with
      | Sum.inl _ => 0
      | Sum.inr q => P q

  have hL'cts : ∀ q : ↥S, L' (Sum.inr q) ≤ continuousH1 (extArithLoc S (Sum.inr q))
      (Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p))) := by
    intro q
    by_cases h₁ : q ∈ T₁
    · rw [hL'₁ q h₁]; exact bot_le
    by_cases h₀ : q ∈ T₀
    · exact (menu_eq_continuousH1_of_mem_iff S _ q _ (hL'₀ q h₀)).le
    have hq : q ∉ T₁ ∪ T₀ := by simp [h₁, h₀]
    refine menu_le_continuousH1 S _ q _ fun x hx => ?_
    obtain ⟨c, hF, -, hc⟩ := (hL'ur q hq x).1 hx
    exact ⟨c, hF, hc⟩

  have hle := greenbergWilesLeAdm_extArithLoc_of_isTheta1_eval_of_ne_two hp2 S hpS (M.dualTwist (cycloChar p)) hsm'
    hMur' adm' hadm' (adm.comap (H1congr e).toLinearMap) hadm₂ hinf' pairing L' hL'cts inv hinv θ hθ
    hbij (fun q x y => hP q x y)

  have hdual : ∀ v, ∀ y : H1 (Rep.res (extArithLoc S v) ((M.dualTwist (cycloChar p)).dualTwist (cycloChar p))),
      y ∈ continuousH1 (extArithLoc S v)
        (Rep.res (extArithLoc S v) ((M.dualTwist (cycloChar p)).dualTwist (cycloChar p))) →
      y ∈ dualConditions (extArithLoc S) (M.dualTwist (cycloChar p))
        ((M.dualTwist (cycloChar p)).dualTwist (cycloChar p)) pairing L' v →
      y ∈ (L v).comap (H1congr ((Rep.resFunctor (extArithLoc S v)).mapIso e)).toLinearMap := by
    intro v y hyc hyd
    cases v with
    | inl u =>
      obtain ⟨⟩ := u
      rw [Subsingleton.elim y 0]
      exact Submodule.zero_mem _
    | inr q =>
      have hdet := (mem_orthogonal_iff_of_agree_on_continuous (extArithLoc S (Sum.inr q)) (P q) (θ q)
        (hP q) (L' (Sum.inr q)) (hL'cts q) ⟨y, hyc⟩).1 hyd
      by_cases h₀ : q ∈ T₀
      ·
        have hLq := menu_eq_continuousH1_of_mem_iff S (M.dualTwist (cycloChar p)) q _ (hL'₀ q h₀)
        have hy0 : (⟨y, hyc⟩ : continuousH1 (extArithLoc S (Sum.inr q)) (Rep.res (extArithLoc S (Sum.inr q))
            ((M.dualTwist (cycloChar p)).dualTwist (cycloChar p)))) = 0 :=
          (theta1_nondegenerate_of_bijective (extArithLoc S (Sum.inr q)) (θ q) (hbij q)).2 ⟨y, hyc⟩
            fun x => hdet x.1 (by rw [hLq]; exact x.2)
        have : y = 0 := congrArg Subtype.val hy0
        rw [this]
        exact Submodule.zero_mem _
      by_cases h₁ : q ∈ T₁
      ·
        refine Submodule.mem_comap.2 ?_
        rw [menu_eq_continuousH1_of_mem_iff S M q _ (hL₁ q h₁)]
        have hcl : ContinuityClause (extArithLoc S (Sum.inr q)) _ y := (mem_continuousH1_iff _ _ y).1 hyc
        exact (mem_continuousH1_iff _ _ _).2
          ((continuityClause_congr (extArithLoc S (Sum.inr q)) ((Rep.resFunctor _).mapIso e) y).1 hcl)
      have hq : q ∉ T₁ ∪ T₀ := by simp [h₁, h₀]
      have hqp : q ≠ ⟨pPrime p, hpS⟩ := fun h => hq (h ▸ hpT)
      exact mem_unramifiedMenu_of_orthogonal S hpS (M.dualTwist (cycloChar p)) hsm' q hqp (inv q)
        (θ q) (hθ q) (hbij q) (L' (Sum.inr q)) (hL'ur q hq) _
        (fun x => (Submodule.mem_comap.trans (hLur q hq _)).trans
          (unramifiedClause_congr (extArithLoc S (Sum.inr q)) ((primeLocalPlace q.1).inertiaSubgroupIn ℚ)
            ((Rep.resFunctor _).mapIso e) x).symm)
        ⟨y, hyc⟩ fun x hx _ => hdet x hx

  have hmenu := le_menu_of_greenbergWilesLeAdm S (M.dualTwist (cycloChar p))
    ((M.dualTwist (cycloChar p)).dualTwist (cycloChar p)) pairing L'
    (fun v => (L v).comap (H1congr ((Rep.resFunctor (extArithLoc S v)).mapIso e)).toLinearMap)
    adm' (adm.comap (H1congr e).toLinearMap) hcts₂ hdual hle

  have hinv₀ := finrank_invariants_congr e
  have hsel := finrank_selmerAdm_congr (extArithLoc S) e
    (fun v => (L v).comap (H1congr ((Rep.resFunctor (extArithLoc S v)).mapIso e)).toLinearMap)
    (adm.comap (H1congr e).toLinearMap)
  rw [condCongr_comap, map_comap_H1congr] at hsel
  omega

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
    (T₁ T₀ : Finset ↥S) (hT : Disjoint T₁ T₀) (hpT : (⟨pPrime p, hpS⟩ : ↥S) ∈ T₁ ∪ T₀)
    (L : ∀ v, Submodule (ZMod p) (H1 (Rep.res (extArithLoc S v) M)))
    (L' : ∀ v, Submodule (ZMod p) (H1 (Rep.res (extArithLoc S v) (M.dualTwist (cycloChar p)))))

    (hL₁ : ∀ q ∈ T₁, ∀ x, x ∈ L (Sum.inr q) ↔
      ∃ c : cocycles₁ (Rep.res (extArithLoc S (Sum.inr q)) M),
        (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
          ∀ g s, extArithLoc S (Sum.inr q) s ∈ F.fixingSubgroup → c.val (g * s) = c.val g) ∧
        H1π _ c = x)
    (hL'₁ : ∀ q ∈ T₁, L' (Sum.inr q) = ⊥)

    (hL₀ : ∀ q ∈ T₀, L (Sum.inr q) = ⊥)
    (hL'₀ : ∀ q ∈ T₀, ∀ x, x ∈ L' (Sum.inr q) ↔
      ∃ c : cocycles₁ (Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p))),
        (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
          ∀ g s, extArithLoc S (Sum.inr q) s ∈ F.fixingSubgroup → c.val (g * s) = c.val g) ∧
        H1π _ c = x)

    (hLur : ∀ q : ↥S, q ∉ T₁ ∪ T₀ → ∀ x, x ∈ L (Sum.inr q) ↔
      ∃ c : cocycles₁ (Rep.res (extArithLoc S (Sum.inr q)) M),
        (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
          ∀ g s, extArithLoc S (Sum.inr q) s ∈ F.fixingSubgroup → c.val (g * s) = c.val g) ∧
        (∃ m : M, ∀ s, extArithLoc S (Sum.inr q) s ∈ (primeLocalPlace q.1).inertiaSubgroupIn ℚ →
          c.val s = (Rep.res (extArithLoc S (Sum.inr q)) M).ρ s m - m) ∧
        H1π _ c = x)
    (hL'ur : ∀ q : ↥S, q ∉ T₁ ∪ T₀ → ∀ x, x ∈ L' (Sum.inr q) ↔
      ∃ c : cocycles₁ (Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p))),
        (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
          ∀ g s, extArithLoc S (Sum.inr q) s ∈ F.fixingSubgroup → c.val (g * s) = c.val g) ∧
        (∃ m : M.dualTwist (cycloChar p),
          ∀ s, extArithLoc S (Sum.inr q) s ∈ (primeLocalPlace q.1).inertiaSubgroupIn ℚ →
          c.val s = (Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p))).ρ s m - m) ∧
        H1π _ c = x) :
    finrank (ZMod p) (selmerAdm (extArithLoc S) M L adm)
        + finrank (ZMod p) (M.dualTwist (cycloChar p)).ρ.invariants
        + ∑ v, finrank (ZMod p) (Rep.res (extArithLoc S v) M).ρ.invariants
      = finrank (ZMod p) (selmerAdm (extArithLoc S) (M.dualTwist (cycloChar p)) L' adm')
        + finrank (ZMod p) M.ρ.invariants
        + ∑ v, finrank (ZMod p) (L v) :=
  GreenbergWilesMenu.assemble
    (selmer_finrank_le hp2 S hpS M hsm hMur adm hadm adm' hadm' T₁ T₀ hT hpT L L' hL₁ hL'₁ hL₀ hL'₀ hLur hL'ur)
    (selmer_finrank_ge hp2 S hpS M hsm hMur adm hadm adm' hadm' T₁ T₀ hT hpT L L' hL₁ hL'₁ hL₀ hL'₀ hLur hL'ur)
    (GreenbergWilesMenu.sum_balance (hp2 := hp2) (S := S) (hpS := hpS) (M := M) (T₁ := T₁) (T₀ := T₀)
      (L := L) (L' := L') (hsm := hsm) (hpT := hpT) (hL₁ := hL₁) (hL'₁ := hL'₁) (hL₀ := hL₀)
      (hL'₀ := hL'₀) (hLur := hLur) (hL'ur := hL'ur)
      (hinf := subsingleton_H1_archSlot hp2 S M))

end S_groupCohomology_greenbergWiles_eq_unramifiedMenu_extArithLoc
end P2MW
export P2MW.S_groupCohomology_greenbergWiles_eq_unramifiedMenu_extArithLoc (solution)
