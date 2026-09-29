-- Prove2me | solution 1 for groupCohomology.greenbergWiles_le_strict_relaxed_continuousH1S
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/65161bf7-f3ff-50f5-b4a7-34f4eb7bb8ee

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_GroupCohomology_SelmerAdm
import Theorems.Thm_groupCohomology_greenbergWiles_eq_unramifiedMenu_extArithLoc
import Theorems.Thm_groupCohomology_subsingleton_H1_of_isUnit_card
import Theorems.Thm_groupCohomology_map_apply_mem_continuousH1_comp
import Theorems.Thm_groupCohomology_eq_continuousH1S_of_forall_mem_iff
import Theorems.Thm_groupCohomology_finiteDimensional_continuousH1S
import Theorems.Thm_ExtCitation_cycloChar_eq_one_of_apply_eq_self_of_isPrimitiveRoot
import Theorems.Thm_ValuationSubring_smul_eq_self_of_mem_inertiaSubgroupIn_of_pow_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_greenbergWiles_le_strict_relaxed_continuousH1S
p2m_attr_erase "instance" "M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion NumberField.AdelicHaar.locallyCompactSpace_adeleRing NumberField.AdelicHaar.finite_residueField_adicCompletionIntegers NumberField.AdelicHaar.locallyCompactSpace_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_finiteAdeleRing NumberField.AdelicHaar.compactSpace_adicCompletionIntegers NumberField.AdelicHaar.t2Space_finiteAdeleRing NumberField.AdelicHaar.t2Space_matrix_adeleRing NumberField.AdelicHaar.t2Space_adeleRing NumberField.AdelicHaar.fact_isOpen_adicCompletionIntegers NumberField.AdelicHaar.t2Space_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_matrix_adeleRing NumberField.AdelicHaar.t2Space_infiniteAdeleRing NumberField.AdelicHaar.properSpace_adicCompletion M4aHerbrand.Bridge.instT2SpaceAdeleRing LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite Deep.NTSupply.instNormalRayClassSubgroup"
p2m_attr_erase "instance" "instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal AlgebraicClosure.Rat.isGalois groupCohomology.Kummer.instMulDistribMulActionRootsOfUnity groupCohomology.normal_comap_fixingSubgroup groupCohomology.finiteIndex_comap_fixingSubgroup Rep.relationCarrier.instAddCommGroup NumberField.LevelArith.instCommGroupUnitsModPow groupCohomology.instMulDistribMulActionGaloisSUnits"
p2m_attr_erase "simp" "groupCohomology.cup_apply groupCohomology.cupCochain_apply groupCohomology.H1desc_H1π groupCohomology.unitsInflate₁_apply groupCohomology.unitsInflate₂_apply M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk M4aHerbrand.IdeleGaloisDescent.classAct_mk M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq ExtCitation.LocalLevel.coe_smul_OO GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl NumberField.SUnits.val_zsmul NumberField.SUnits.val_add M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply"
p2m_attr_erase "simp" "FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq M4aHerbrand.Bridge.finiteConorm_apply SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id"
p2m_attr_erase "simp" "TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply"
p2m_attr_erase "simp" "AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq IsLocalRing.principalUnits_zero Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec groupCohomology.Kummer.coe_kummerCocycleRoots groupCohomology.Kummer.mem_powerSubgroup_iff groupCohomology.Kummer.val_smul_units"
p2m_attr_erase "simp" "groupCohomology.Kummer.kummerHom_apply groupCohomology.Kummer.coe_smul_rootsOfUnity groupCohomology.levelQuotientEquiv_mk groupCohomology.levelQuotientHom_mk Rep.toIntRepρ_apply_apply Rep.toIntRep_ρ Rep.toIntRepMap_hom_apply M4aHerbrand.AdeleBaseChange.classNorm_mk M4aHerbrand.AdeleBaseChange.coe_idelesMap_apply M4aHerbrand.AdeleBaseChange.classMap_mk M4aHerbrand.repHomResOfMulEquivariant_hom_apply M4aHerbrand.AdeleBaseChange.sClassNorm_mk M4aHerbrand.AdeleBaseChange.sClassMap_mk NumberField.SArchIdele.fibre_inl NumberField.SArchIdele.toSIdele_hom_apply_inr NumberField.SArchIdele.toSIdele_hom_apply_inl_inr NumberField.SArchIdele.toSIdele_hom_apply_inl_inl NumberField.SArchIdele.fibre_inr Representation.TateResCor.cosetDecomp_apply Rep.coe_tateHneg1Res_apply Representation.TateResCor.coe_tateHneg1Cores_apply Representation.TateResCor.tateH0Res_mk Rep.coe_tateHneg1Cores_apply Rep.tateH0Res_mk Representation.TateResCor.coe_cosetNormInvariants_apply Rep.tateH0Cores_mk Representation.TateResCor.coinvariantsCores_mk Representation.TateResCor.coinvariantsTransfer_mk Representation.TateResCor.tateH0Cores_mk Representation.TateResCor.coe_tateHneg1Res_apply Rep.coe_tateδneg2_apply Rep.splittingShortComplex_X₃ Rep.splittingShortComplex_X₁ Rep.splittingShortComplex_X₂ Rep.splittingShortComplex_f Rep.augShortComplex_f Rep.augShortComplex_X₃ Rep.cocycleTwist_single Rep.augShortComplex_X₂ Rep.splittingModuleι_hom_apply"
p2m_attr_erase "simp" "Rep.augShortComplex_X₁ Rep.splittingShortComplex_g Rep.augShortComplex_g Rep.splittingModuleπ_hom_apply Rep.coe_dimShiftDownObjMap_apply groupCohomology.continuousH2Inflation_H2π groupCohomology.levelInflate₂_apply groupCohomology.coe_levelInflateCocycles₂ groupCohomology.levelInflate₁_apply NumberField.LevelArith.coe_levelFieldEquiv NumberField.LevelArith.modP_apply_mk NumberField.LevelArith.coe_levelFieldEquiv_symm NumberField.LevelArith.torsionP_apply_coe NumberField.LevelArith.repTorsionPMap_hom_apply_coe NumberField.LevelArith.toZMod_apply NumberField.LevelArith.repModPMap_hom_mk groupCohomology.coe_continuousH1SrMap_apply groupCohomology.continuousH2SrMap_continuousH2Srπ groupCohomology.coe_levelCocyclesSr₂Map NumberField.LevelArith.smul_mk NumberField.LevelArith.selmerRepInt_ρ_apply NumberField.LevelArith.selmerRepField_ρ_apply NumberField.LevelArith.unitsModPowMap_mk groupCohomology.frobeniusOnCoinvariants_mk groupCohomology.evalAtGen_apply Rep.quotientRightTranslation_hom_single Rep.quotientRightTranslationTwist_hom_apply groupCohomology.coe_smul_galoisSUnits groupCohomology.galoisSUnitsToUnits_apply"

set_option autoImplicit false
open CategoryTheory Module groupCohomology ExtCitation IntermediateField

noncomputable section

namespace P2mGWInst

abbrev Qb := AlgebraicClosure ℚ
abbrev Γ := AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ

scoped instance isAlgebraicQbar : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
  convert AlgebraicClosure.isAlgebraic ℚ <;> first | with_reducible_and_instances rfl | exact Subsingleton.elim _ _
scoped instance isAlgClosureQbar : IsAlgClosure ℚ (AlgebraicClosure ℚ) := by
  convert AlgebraicClosure.instIsAlgClosure ℚ <;> first | with_reducible_and_instances rfl | exact Subsingleton.elim _ _

theorem isIntegral_algebraicClosure_rat : Algebra.IsIntegral ℚ (AlgebraicClosure ℚ) := by
  have h := Subsingleton.elim (AlgebraicClosure.instAlgebra ℚ) (DivisionRing.toRatAlgebra)
  have := AlgebraicClosure.isAlgebraic ℚ
  rw [h] at this
  exact Algebra.IsAlgebraic.isIntegral

private lemma _root_.P2mGWInst.exists_isPrimitiveRoot (N : ℕ) [NeZero N] : ∃ ζ₀ : Qb, IsPrimitiveRoot ζ₀ N :=
  IsCyclotomicExtension.exists_isPrimitiveRoot (S := ({N} : Set ℕ)) Qb Qb
    (Set.mem_singleton N) (NeZero.ne N)

p2m_export "P2mGWInst" "exists_isPrimitiveRoot"

section Adm

variable {k : Type} [CommRing k] (M : Rep k Γ)

def admSub (S₀ : Finset Nat.Primes) : Submodule k (H1 M) where
  carrier := {x | ∃ c : cocycles₁ M, IsLocallyConstant ⇑c ∧
      (∀ q : Nat.Primes, q ∉ S₀ → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
        A.LiesOverPrime (q : ℕ) → ∃ m : M, ∀ g ∈ A.inertiaSubgroupIn ℚ, c g = M.ρ g m - m) ∧
      H1π M c = x}
  zero_mem' := ⟨0, IsLocallyConstant.const (0 : M), fun q _ A _ =>
    ⟨0, fun g _ => by change (0 : M) = _; simp⟩, map_zero _⟩
  add_mem' := by
    rintro x y ⟨c, hc, hcq, rfl⟩ ⟨d, hd, hdq, rfl⟩
    refine ⟨c + d, ?_, fun q hq A hA => ?_, map_add _ _ _⟩
    · have : ⇑(c + d) = ⇑c + ⇑d := rfl
      rw [this]
      exact hc.add hd
    · obtain ⟨m, hm⟩ := hcq q hq A hA
      obtain ⟨m', hm'⟩ := hdq q hq A hA
      refine ⟨m + m', fun g hg => ?_⟩
      have : (c + d) g = c g + d g := rfl
      rw [this, hm g hg, hm' g hg, map_add]
      abel
  smul_mem' := by
    rintro a x ⟨c, hc, hcq, rfl⟩
    refine ⟨a • c, ?_, fun q hq A hA => ?_, map_smul _ _ _⟩
    · have : ⇑(a • c) = (fun m : M => a • m) ∘ ⇑c := rfl
      rw [this]
      exact hc.comp _
    · obtain ⟨m, hm⟩ := hcq q hq A hA
      refine ⟨a • m, fun g hg => ?_⟩
      have : (a • c) g = a • c g := rfl
      rw [this, hm g hg, map_smul, smul_sub]

lemma mem_admSub_iff (S₀ : Finset Nat.Primes) (x : H1 M) :
    x ∈ admSub M S₀ ↔ ∃ c : cocycles₁ M, IsLocallyConstant ⇑c ∧
      (∀ q : Nat.Primes, q ∉ S₀ → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
        A.LiesOverPrime (q : ℕ) → ∃ m : M, ∀ g ∈ A.inertiaSubgroupIn ℚ, c g = M.ρ g m - m) ∧
      H1π M c = x := Iff.rfl

end Adm

section Dual

variable {p : ℕ} [Fact p.Prime] (M : Rep (ZMod p) Γ)

lemma exists_level [FiniteDimensional (ZMod p) M]
    (hsm : ∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s ∈ F.fixingSubgroup, M.ρ s m = m) :
    ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s ∈ F.fixingSubgroup, M.ρ s = 1 := by
  classical
  let b := Module.finBasis (ZMod p) M
  choose F hFfd hF using fun i => hsm (b i)
  haveI : ∀ i, FiniteDimensional ℚ (F i) := hFfd
  refine ⟨⨆ i, F i, IntermediateField.finiteDimensional_iSup_of_finite, fun s hs => ?_⟩
  refine b.ext fun i => ?_
  rw [Module.End.one_apply]
  exact hF i s (IntermediateField.fixingSubgroup_antitone (le_iSup F i) hs)

lemma dualTwist_ρ_eq_self {g : Γ} (h1 : M.ρ g⁻¹ = 1) (h2 : cycloChar p g = 1)
    (f : M.dualTwist (cycloChar p)) : (M.dualTwist (cycloChar p)).ρ g f = f := by
  rw [Rep.dualTwist_ρ_apply, h1, h2, Units.val_one, one_smul, Module.End.one_eq_id,
    LinearMap.comp_id]

lemma hsm_dual [FiniteDimensional (ZMod p) M]
    (hsm : ∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s ∈ F.fixingSubgroup, M.ρ s m = m) :
    ∀ f : M.dualTwist (cycloChar p),
      ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
        ∀ s ∈ F.fixingSubgroup, (M.dualTwist (cycloChar p)).ρ s f = f := by
  intro f
  obtain ⟨L, hLfd, hL⟩ := exists_level M hsm
  haveI := hLfd
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot p
  have hζint : IsIntegral ℚ ζ := (isIntegral_algebraicClosure_rat).isIntegral ζ
  haveI : FiniteDimensional ℚ ℚ⟮ζ⟯ := adjoin.finiteDimensional hζint
  refine ⟨L ⊔ ℚ⟮ζ⟯, finiteDimensional_sup L ℚ⟮ζ⟯, fun s hs => ?_⟩
  have hsL : s ∈ L.fixingSubgroup := IntermediateField.fixingSubgroup_antitone le_sup_left hs
  have hsζ : s ζ = ζ :=
    (mem_fixingSubgroup_iff (K := L ⊔ ℚ⟮ζ⟯) s).mp hs ζ
      (le_sup_right (a := L) (mem_adjoin_simple_self ℚ ζ))
  have h1 : M.ρ s⁻¹ = 1 := hL s⁻¹ (inv_mem hsL)
  have h2 : cycloChar p s = 1 := cycloChar_eq_one_of_apply_eq_self_of_isPrimitiveRoot p s hζ hsζ
  exact dualTwist_ρ_eq_self M h1 h2 f

lemma hMur_dual (S' : Finset Nat.Primes) (hpS : pPrime p ∈ S')
    (hMur : ∀ q : Nat.Primes, q ∉ S' → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
      A.LiesOverPrime (q : ℕ) → ∀ g ∈ A.inertiaSubgroupIn ℚ, M.ρ g = 1) :
    ∀ q : Nat.Primes, q ∉ S' → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
      A.LiesOverPrime (q : ℕ) → ∀ g ∈ A.inertiaSubgroupIn ℚ,
        (M.dualTwist (cycloChar p)).ρ g = 1 := by
  intro q hq A hA g hg
  have hp : p.Prime := Fact.out
  have hqp : ¬ (q : ℕ) ∣ p := by
    intro hdvd
    have : (q : ℕ) = p := (Nat.prime_dvd_prime_iff_eq q.2 hp).mp hdvd
    apply hq
    have hq' : q = pPrime p := Subtype.ext this
    rw [hq']; exact hpS
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot p
  have hgζ : g ζ = ζ :=
    ValuationSubring.smul_eq_self_of_mem_inertiaSubgroupIn_of_pow_eq_one A q.2 hA hg hqp
      hζ.pow_eq_one
  have h2 : cycloChar p g = 1 := cycloChar_eq_one_of_apply_eq_self_of_isPrimitiveRoot p g hζ hgζ
  have h1 : M.ρ g⁻¹ = 1 := hMur q hq A hA g⁻¹ (inv_mem hg)
  ext f : 1
  rw [Module.End.one_apply]
  exact dualTwist_ρ_eq_self M h1 h2 f

end Dual

section Menu

variable {p : ℕ} [Fact p.Prime]

open Classical in
def menuL (S' Q : Finset Nat.Primes) (M : Rep (ZMod p) Γ) :
    ∀ v : extArithIndex S', Submodule (ZMod p) (H1 (Rep.res (extArithLoc S' v) M))
  | Sum.inl _ => ⊤
  | Sum.inr q => if (q : Nat.Primes) ∈ Q then
      continuousH1 (extArithLoc S' (Sum.inr q)) (Rep.res (extArithLoc S' (Sum.inr q)) M) else ⊥

open Classical in
def menuL' (S' Q : Finset Nat.Primes) (M : Rep (ZMod p) Γ) :
    ∀ v : extArithIndex S', Submodule (ZMod p) (H1 (Rep.res (extArithLoc S' v) M))
  | Sum.inl _ => ⊤
  | Sum.inr q => if (q : Nat.Primes) ∈ Q then ⊥ else
      continuousH1 (extArithLoc S' (Sum.inr q)) (Rep.res (extArithLoc S' (Sum.inr q)) M)

variable (S' Q : Finset Nat.Primes) (M : Rep (ZMod p) Γ)

lemma menuL_inr_of_mem (q : ↥S') (hq : (q : Nat.Primes) ∈ Q) :
    menuL S' Q M (Sum.inr q) =
      continuousH1 (extArithLoc S' (Sum.inr q)) (Rep.res (extArithLoc S' (Sum.inr q)) M) := by
  simp [menuL, hq]

lemma menuL_inr_of_not_mem (q : ↥S') (hq : (q : Nat.Primes) ∉ Q) :
    menuL S' Q M (Sum.inr q) = ⊥ := by
  simp [menuL, hq]

lemma menuL'_inr_of_mem (q : ↥S') (hq : (q : Nat.Primes) ∈ Q) :
    menuL' S' Q M (Sum.inr q) = ⊥ := by
  simp [menuL', hq]

lemma menuL'_inr_of_not_mem (q : ↥S') (hq : (q : Nat.Primes) ∉ Q) :
    menuL' S' Q M (Sum.inr q) =
      continuousH1 (extArithLoc S' (Sum.inr q)) (Rep.res (extArithLoc S' (Sum.inr q)) M) := by
  simp [menuL', hq]

lemma menuL_inl (u : Unit) : menuL S' Q M (Sum.inl u) = ⊤ := rfl
lemma menuL'_inl (u : Unit) : menuL' S' Q M (Sum.inl u) = ⊤ := rfl

lemma mem_continuousH1_iff' {G : Type} [Group G] (r : G →* Γ) (A : Rep (ZMod p) G) (x : H1 A) :
    x ∈ continuousH1 r A ↔
      ∃ c : cocycles₁ A,
        (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
          ∀ g s, r s ∈ F.fixingSubgroup → c.val (g * s) = c.val g) ∧
        H1π _ c = x := by
  rw [mem_continuousH1_iff]
  rfl

end Menu

section Arch

variable {p : ℕ} [Fact p.Prime]

lemma finite_arch : Finite ↥archimedeanDecomposition := by
  unfold archimedeanDecomposition
  have : IsOfFinOrder complexConjugation :=
    isOfFinOrder_iff_pow_eq_one.2 ⟨2, by norm_num, complexConjugation_sq⟩
  exact this.finite_zpowers

lemma natCard_arch_dvd : Nat.card ↥archimedeanDecomposition ∣ 2 := by
  unfold archimedeanDecomposition
  rw [Nat.card_zpowers]
  exact orderOf_dvd_of_pow_eq_one complexConjugation_sq

lemma subsingleton_H1_arch (hp2 : p ≠ 2) (S' : Finset Nat.Primes) (M : Rep (ZMod p) Γ) :
    Subsingleton (H1 (Rep.res (extArithLoc S' (Sum.inl ())) M)) := by
  haveI : Finite (extArithLocalGroups S' (Sum.inl ())) := finite_arch
  letI : Fintype (extArithLocalGroups S' (Sum.inl ())) := Fintype.ofFinite _
  apply groupCohomology.subsingleton_H1_of_isUnit_card
  have hcard : Fintype.card (extArithLocalGroups S' (Sum.inl ())) ∣ 2 := by
    rw [Fintype.card_eq_nat_card]; exact natCard_arch_dvd
  have h2 : IsUnit ((2 : ℕ) : ZMod p) := by
    rw [isUnit_iff_ne_zero, Ne, ZMod.natCast_eq_zero_iff]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).1 h)
  exact isUnit_of_dvd_unit (Nat.cast_dvd_cast hcard) h2

lemma sum_extArithIndex (S' : Finset Nat.Primes) (f : extArithIndex S' → ℕ) :
    ∑ v, f v = f (Sum.inl ()) + ∑ q : ↥S', f (Sum.inr q) := by
  change ∑ v : Unit ⊕ ↥S', f v = _
  rw [Fintype.sum_sum_type]
  simp

end Arch

theorem main
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (S Q : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (hSQ : Disjoint S Q)
    (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    [FiniteDimensional (ZMod p) M]
    (hsm : ∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s ∈ F.fixingSubgroup, M.ρ s m = m)
    (hMur : ∀ q : Nat.Primes, q ∉ S ∪ Q → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
      A.LiesOverPrime (q : ℕ) → ∀ g ∈ A.inertiaSubgroupIn ℚ, M.ρ g = 1) :
    finrank (ZMod p) ↥(continuousH1S (S ∪ Q) M ⊓
        ⨅ q ∈ S, LinearMap.ker (map (primeLocalToGlobal q)
          (𝟙 (Rep.res (primeLocalToGlobal q) M)) 1).hom)
      + finrank (ZMod p) (M.dualTwist (cycloChar p)).ρ.invariants
      + finrank (ZMod p) (Rep.res archimedeanLoc M).ρ.invariants
      + ∑ q ∈ S ∪ Q, finrank (ZMod p) (Rep.res (primeLocalToGlobal q) M).ρ.invariants
    ≤ finrank (ZMod p) ↥(continuousH1S (S ∪ Q) (M.dualTwist (cycloChar p)) ⊓
        ⨅ q ∈ Q, LinearMap.ker (map (primeLocalToGlobal q)
          (𝟙 (Rep.res (primeLocalToGlobal q) (M.dualTwist (cycloChar p)))) 1).hom)
      + finrank (ZMod p) M.ρ.invariants
      + ∑ q ∈ Q, finrank (ZMod p)
          ↥(continuousH1 (primeLocalToGlobal q) (Rep.res (primeLocalToGlobal q) M)) := by
  classical
  set S' : Finset Nat.Primes := S ∪ Q with hS'
  have hpS' : pPrime p ∈ S' := Finset.mem_union_left _ hpS

  have hsm' := hsm_dual M hsm
  have hMur' := hMur_dual M S' hpS' hMur
  have hadm : admSub M S' = continuousH1S S' M :=
    groupCohomology.eq_continuousH1S_of_forall_mem_iff S' M hMur (admSub M S')
      (mem_admSub_iff M S')
  have hadm' : admSub (M.dualTwist (cycloChar p)) S' = continuousH1S S' (M.dualTwist (cycloChar p)) :=
    groupCohomology.eq_continuousH1S_of_forall_mem_iff S' (M.dualTwist (cycloChar p)) hMur' (admSub (M.dualTwist (cycloChar p)) S')
      (mem_admSub_iff (M.dualTwist (cycloChar p)) S')
  haveI hfinM' : FiniteDimensional (ZMod p) (M.dualTwist (cycloChar p)) := by
    change FiniteDimensional (ZMod p) (Module.Dual (ZMod p) M)
    infer_instance
  haveI : FiniteDimensional (ZMod p) (continuousH1S S' M) :=
    groupCohomology.finiteDimensional_continuousH1S S' M hsm
  haveI : FiniteDimensional (ZMod p) (continuousH1S S' (M.dualTwist (cycloChar p))) :=
    groupCohomology.finiteDimensional_continuousH1S S' (M.dualTwist (cycloChar p)) hsm'
  haveI : FiniteDimensional (ZMod p) (admSub M S') := by rw [hadm]; infer_instance
  haveI : FiniteDimensional (ZMod p) (admSub (M.dualTwist (cycloChar p)) S') := by rw [hadm']; infer_instance

  let T₀ : Finset ↥S' := Finset.univ.filter fun q => (q : Nat.Primes) ∈ S
  let T₁ : Finset ↥S' := Finset.univ.filter fun q => (q : Nat.Primes) ∈ Q
  have hT : Disjoint T₁ T₀ := by
    rw [Finset.disjoint_filter]
    intro q _ hqQ hqS
    exact Finset.disjoint_left.1 hSQ hqS hqQ
  have hpT : (⟨pPrime p, hpS'⟩ : ↥S') ∈ T₁ ∪ T₀ :=
    Finset.mem_union_right _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, hpS⟩)
  have hcover : ∀ q : ↥S', q ∈ T₁ ∪ T₀ := by
    intro q
    rcases Finset.mem_union.1 q.2 with h | h
    · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
  have hT₁ : ∀ q : ↥S', q ∈ T₁ ↔ (q : Nat.Primes) ∈ Q := fun q => by simp [T₁]
  have hT₀ : ∀ q : ↥S', q ∈ T₀ ↔ (q : Nat.Primes) ∈ S := fun q => by simp [T₀]
  have hT₀' : ∀ q : ↥S', q ∈ T₀ → (q : Nat.Primes) ∉ Q := fun q hq hqQ =>
    Finset.disjoint_left.1 hSQ ((hT₀ q).1 hq) hqQ

  have hGW := groupCohomology.greenbergWiles_eq_unramifiedMenu_extArithLoc hp2 S' hpS' M hsm hMur
    (admSub M S') (mem_admSub_iff M S') (admSub (M.dualTwist (cycloChar p)) S') (mem_admSub_iff (M.dualTwist (cycloChar p)) S') T₁ T₀ hT hpT
    (menuL S' Q M) (menuL' S' Q (M.dualTwist (cycloChar p)))
    (fun q hq x => by
      rw [menuL_inr_of_mem S' Q M q ((hT₁ q).1 hq)]
      exact mem_continuousH1_iff' _ _ x)
    (fun q hq => menuL'_inr_of_mem S' Q (M.dualTwist (cycloChar p)) q ((hT₁ q).1 hq))
    (fun q hq => menuL_inr_of_not_mem S' Q M q (hT₀' q hq))
    (fun q hq x => by
      rw [menuL'_inr_of_not_mem S' Q (M.dualTwist (cycloChar p)) q (hT₀' q hq)]
      exact mem_continuousH1_iff' _ _ x)
    (fun q hq => absurd (hcover q) hq)
    (fun q hq => absurd (hcover q) hq)

  have hSel : finrank (ZMod p) ↥(continuousH1S S' M ⊓
      ⨅ q ∈ S, LinearMap.ker (map (primeLocalToGlobal q)
        (𝟙 (Rep.res (primeLocalToGlobal q) M)) 1).hom) ≤
      finrank (ZMod p) ↥(selmerAdm (extArithLoc S') M (menuL S' Q M) (admSub M S')) := by
    apply Submodule.finrank_mono
    intro x hx
    rw [Submodule.mem_inf] at hx
    obtain ⟨hxc, hxk⟩ := hx
    rw [mem_selmerAdm_iff]
    refine ⟨fun v => ?_, by rw [hadm]; exact hxc⟩
    cases v with
    | inl u => rw [menuL_inl]; exact Submodule.mem_top
    | inr q =>
      by_cases hq : (q : Nat.Primes) ∈ Q
      · rw [menuL_inr_of_mem S' Q M q hq]
        exact groupCohomology.map_apply_mem_continuousH1_comp (MonoidHom.id Γ)
          (extArithLoc S' (Sum.inr q)) M x (continuousH1S_le_continuousH1 S' M hxc)
      · rw [menuL_inr_of_not_mem S' Q M q hq, Submodule.mem_bot]
        have hqS : (q : Nat.Primes) ∈ S := (Finset.mem_union.1 q.2).resolve_right hq
        have := (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hxk (q : Nat.Primes)) hqS
        exact this

  have hSel' : finrank (ZMod p) ↥(selmerAdm (extArithLoc S') (M.dualTwist (cycloChar p)) (menuL' S' Q (M.dualTwist (cycloChar p))) (admSub (M.dualTwist (cycloChar p)) S')) ≤
      finrank (ZMod p) ↥(continuousH1S S' (M.dualTwist (cycloChar p)) ⊓
        ⨅ q ∈ Q, LinearMap.ker (map (primeLocalToGlobal q)
          (𝟙 (Rep.res (primeLocalToGlobal q) (M.dualTwist (cycloChar p)))) 1).hom) := by
    apply Submodule.finrank_mono
    intro x hx
    rw [mem_selmerAdm_iff] at hx
    obtain ⟨hL, hxadm⟩ := hx
    rw [hadm'] at hxadm
    refine Submodule.mem_inf.2 ⟨hxadm, ?_⟩
    refine (Submodule.mem_iInf _).2 fun q => (Submodule.mem_iInf _).2 fun hq => ?_
    have hqS' : q ∈ S' := Finset.mem_union_right _ hq
    have := hL (Sum.inr ⟨q, hqS'⟩)
    rw [menuL'_inr_of_mem S' Q (M.dualTwist (cycloChar p)) ⟨q, hqS'⟩ hq, Submodule.mem_bot] at this
    exact this

  have hsumH0 : ∑ v, finrank (ZMod p) (Rep.res (extArithLoc S' v) M).ρ.invariants =
      finrank (ZMod p) (Rep.res archimedeanLoc M).ρ.invariants +
        ∑ q ∈ S', finrank (ZMod p) (Rep.res (primeLocalToGlobal q) M).ρ.invariants := by
    rw [sum_extArithIndex]
    congr 1
    exact Finset.sum_coe_sort S'
      (fun q => finrank (ZMod p) (Rep.res (primeLocalToGlobal q) M).ρ.invariants)
  have h0 : finrank (ZMod p) ↥(menuL S' Q M (Sum.inl ())) = 0 := by
    rw [menuL_inl, finrank_top]
    haveI := subsingleton_H1_arch hp2 S' M
    exact Module.finrank_zero_of_subsingleton
  have hsumL : ∑ v, finrank (ZMod p) ↥(menuL S' Q M v) =
      ∑ q ∈ Q, finrank (ZMod p)
        ↥(continuousH1 (primeLocalToGlobal q) (Rep.res (primeLocalToGlobal q) M)) := by
    rw [sum_extArithIndex, h0, zero_add]
    have h1 : ∑ q : ↥S', finrank (ZMod p) ↥(menuL S' Q M (Sum.inr q)) =
        ∑ q : ↥S', (if (q : Nat.Primes) ∈ Q then finrank (ZMod p)
          ↥(continuousH1 (primeLocalToGlobal q) (Rep.res (primeLocalToGlobal (q : Nat.Primes)) M))
          else 0) := by
      refine Finset.sum_congr rfl fun q _ => ?_
      by_cases hq : (q : Nat.Primes) ∈ Q
      · rw [if_pos hq, menuL_inr_of_mem S' Q M q hq]; rfl
      · rw [if_neg hq, menuL_inr_of_not_mem S' Q M q hq, finrank_bot]
    rw [h1, Finset.sum_coe_sort S' (fun q => if q ∈ Q then finrank (ZMod p)
          ↥(continuousH1 (primeLocalToGlobal q) (Rep.res (primeLocalToGlobal q) M)) else 0),
      Finset.sum_ite_mem, Finset.union_inter_cancel_right]

  rw [hsumH0, hsumL] at hGW
  omega

end P2mGWInst
p2m_reactivate "P2MW.S_groupCohomology_greenbergWiles_le_strict_relaxed_continuousH1S.P2mGWInst"

theorem solution
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (S Q : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (hSQ : Disjoint S Q)
    (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    [FiniteDimensional (ZMod p) M]
    (hsm : ∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s ∈ F.fixingSubgroup, M.ρ s m = m)
    (hMur : ∀ q : Nat.Primes, q ∉ S ∪ Q → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
      A.LiesOverPrime (q : ℕ) → ∀ g ∈ A.inertiaSubgroupIn ℚ, M.ρ g = 1) :
    finrank (ZMod p) ↥(continuousH1S (S ∪ Q) M ⊓
        ⨅ q ∈ S, LinearMap.ker (map (primeLocalToGlobal q)
          (𝟙 (Rep.res (primeLocalToGlobal q) M)) 1).hom)
      + finrank (ZMod p) (M.dualTwist (cycloChar p)).ρ.invariants
      + finrank (ZMod p) (Rep.res archimedeanLoc M).ρ.invariants
      + ∑ q ∈ S ∪ Q, finrank (ZMod p) (Rep.res (primeLocalToGlobal q) M).ρ.invariants
    ≤ finrank (ZMod p) ↥(continuousH1S (S ∪ Q) (M.dualTwist (cycloChar p)) ⊓
        ⨅ q ∈ Q, LinearMap.ker (map (primeLocalToGlobal q)
          (𝟙 (Rep.res (primeLocalToGlobal q) (M.dualTwist (cycloChar p)))) 1).hom)
      + finrank (ZMod p) M.ρ.invariants
      + ∑ q ∈ Q, finrank (ZMod p)
          ↥(continuousH1 (primeLocalToGlobal q) (Rep.res (primeLocalToGlobal q) M)) :=
  P2mGWInst.main hp2 S Q hpS hSQ M hsm hMur

end
p2m_reactivate "P2MW.S_groupCohomology_greenbergWiles_le_strict_relaxed_continuousH1S.P2mGWInst"

end S_groupCohomology_greenbergWiles_le_strict_relaxed_continuousH1S
end P2MW
export P2MW.S_groupCohomology_greenbergWiles_le_strict_relaxed_continuousH1S (solution)
