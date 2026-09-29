-- Prove2me | solution 1 for groupCohomology.exists_continuousH2S_locRes_eq_iff_and_surjective_sum_theta2_of_ne_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/b84e00c3-de30-5658-8fa4-198884055c3d

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_GroupCohomology_ContinuousDuality
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_GroupCohomology_LocalInvariant
import Definitions.Def_GroupCohomology_ContinuousH2Map
import Theorems.Thm_groupCohomology_bijective_theta_dualTwist_of_primeLocal
import Theorems.Thm_groupCohomology_exists_theta0_and_theta2
import Theorems.Thm_groupCohomology_exists_theta1
import Theorems.Thm_groupCohomology_isLocalInv_localInv_and_bijective
import Theorems.Thm_groupCohomology_exists_level_ofChar_cycloChar_comp
import Theorems.Thm_groupCohomology_sum_localInv_locRes2S_eq_zero_of_ne_two
import Theorems.Thm_groupCohomology_exists_range_locRes_continuousH2S_sup_eq_top_finrank_le_finrank_invariants_dualTwist_of_ne_two
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_exists_continuousH2S_locRes_eq_iff_and_surjective_sum_theta2_of_ne_two
p2m_attr_erase "instance" "ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal groupCohomology.normal_comap_fixingSubgroup groupCohomology.finiteIndex_comap_fixingSubgroup ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete groupCohomology.Kummer.instMulDistribMulActionRootsOfUnity M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion NumberField.AdelicHaar.locallyCompactSpace_adeleRing NumberField.AdelicHaar.finite_residueField_adicCompletionIntegers NumberField.AdelicHaar.locallyCompactSpace_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_finiteAdeleRing NumberField.AdelicHaar.compactSpace_adicCompletionIntegers NumberField.AdelicHaar.t2Space_finiteAdeleRing NumberField.AdelicHaar.t2Space_matrix_adeleRing NumberField.AdelicHaar.t2Space_adeleRing NumberField.AdelicHaar.fact_isOpen_adicCompletionIntegers"
p2m_attr_erase "instance" "NumberField.AdelicHaar.t2Space_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_matrix_adeleRing NumberField.AdelicHaar.t2Space_infiniteAdeleRing NumberField.AdelicHaar.properSpace_adicCompletion M4aHerbrand.Bridge.instT2SpaceAdeleRing LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite Deep.NTSupply.instNormalRayClassSubgroup instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal AlgebraicClosure.Rat.isGalois groupCohomology.instMulDistribMulActionGaloisSUnits NumberField.LevelArith.instCommGroupUnitsModPow"
p2m_attr_erase "simp" "ExtCitation.LocalLevel.coe_smul_OO WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply groupCohomology.Kummer.coe_kummerCocycleRoots groupCohomology.Kummer.mem_powerSubgroup_iff groupCohomology.Kummer.val_smul_units groupCohomology.Kummer.kummerHom_apply groupCohomology.Kummer.coe_smul_rootsOfUnity IsLocalRing.principalUnits_zero M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk M4aHerbrand.IdeleGaloisDescent.classAct_mk M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl NumberField.SUnits.val_zsmul NumberField.SUnits.val_add M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply"
p2m_attr_erase "simp" "FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq M4aHerbrand.Bridge.finiteConorm_apply SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def"
p2m_attr_erase "simp" "TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply"
p2m_attr_erase "simp" "Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec groupCohomology.coe_continuousH1SrMap_apply groupCohomology.continuousH2SrMap_continuousH2Srπ"
p2m_attr_erase "simp" "groupCohomology.coe_levelCocyclesSr₂Map groupCohomology.coe_smul_galoisSUnits groupCohomology.galoisSUnitsToUnits_apply NumberField.LevelArith.coe_levelFieldEquiv NumberField.LevelArith.modP_apply_mk NumberField.LevelArith.coe_levelFieldEquiv_symm NumberField.LevelArith.torsionP_apply_coe NumberField.LevelArith.repTorsionPMap_hom_apply_coe NumberField.LevelArith.toZMod_apply NumberField.LevelArith.repModPMap_hom_mk NumberField.LevelArith.smul_mk NumberField.LevelArith.selmerRepInt_ρ_apply NumberField.LevelArith.selmerRepField_ρ_apply NumberField.LevelArith.unitsModPowMap_mk groupCohomology.continuousH2Inflation_H2π groupCohomology.levelInflate₂_apply groupCohomology.coe_levelInflateCocycles₂ groupCohomology.levelInflate₁_apply"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
open CategoryTheory Module groupCohomology ExtCitation

noncomputable section
namespace P2M9ca

section PushS

variable (S : Finset Nat.Primes) {k : Type} [CommRing k]
  {A B : Rep k (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)}
  (ψ : A →ₗ[k] B) (hψ : ∀ (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (a : A), ψ (A.ρ g a) = B.ρ g (ψ a))

lemma cochainsPullPush₂_id_eq (x : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → A) :
    cochainsPullPush₂ (MonoidHom.id _) ψ x = ψ ∘ x := by
  funext st; rfl

lemma cochainsPullPush₁_id_eq (x : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → A) :
    cochainsPullPush₁ (MonoidHom.id _) ψ x = ψ ∘ x := by
  funext s; rfl

include hψ in
lemma pushS_mem_levelCocyclesS₂ {x} (hx : x ∈ levelCocyclesS₂ S A) :
    cochainsPullPush₂ (MonoidHom.id _) ψ x ∈ levelCocyclesS₂ S B := by
  refine ⟨cochainsPullPush₂_mem_cocycles₂ (MonoidHom.id _) ψ (fun g a => hψ g a) hx.1, ?_⟩
  rw [cochainsPullPush₂_id_eq]
  exact hx.2.comp ψ

include hψ in
lemma pushS_mem_levelCoboundariesS₂ {x} (hx : x ∈ levelCoboundariesS₂ S A) :
    cochainsPullPush₂ (MonoidHom.id _) ψ x ∈ levelCoboundariesS₂ S B := by
  obtain ⟨y, hy, rfl⟩ := (mem_levelCoboundariesS₂_iff S A x).1 hx
  refine (mem_levelCoboundariesS₂_iff S B _).2 ⟨cochainsPullPush₁ (MonoidHom.id _) ψ y, ?_, ?_⟩
  · rw [cochainsPullPush₁_id_eq]; exact hy.comp ψ
  · exact (cochainsPullPush₂_d₁₂ (MonoidHom.id _) ψ (fun g a => hψ g a) y).symm

def levelCocyclesS₂Map : ↥(levelCocyclesS₂ S A) →ₗ[k] ↥(levelCocyclesS₂ S B) :=
  (cochainsPullPush₂ (MonoidHom.id _) ψ).restrict fun _ hx => pushS_mem_levelCocyclesS₂ S ψ hψ hx

@[scoped simp] lemma coe_levelCocyclesS₂Map (x : ↥(levelCocyclesS₂ S A)) :
    ((levelCocyclesS₂Map S ψ hψ x : ↥(levelCocyclesS₂ S B)) :
      (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → B)
      = ψ ∘ ((x : ↥(levelCocyclesS₂ S A)) :
      (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → A) := rfl

def continuousH2SMap : continuousH2S S A →ₗ[k] continuousH2S S B :=
  Submodule.mapQ _ _ (levelCocyclesS₂Map S ψ hψ) fun _ hx => pushS_mem_levelCoboundariesS₂ S ψ hψ hx

@[scoped simp] lemma continuousH2SMap_mk (x : ↥(levelCocyclesS₂ S A)) :
    continuousH2SMap S ψ hψ (Submodule.Quotient.mk x) = Submodule.Quotient.mk (levelCocyclesS₂Map S ψ hψ x) := rfl

lemma locRes₂S_continuousH2SMap {H : Type} [Group H] (f : H →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (x : continuousH2S S A) :
    locRes₂S S B f (continuousH2SMap S ψ hψ x)
      = continuousH2Map (rH := f) (rG := f) (MonoidHom.id H) (fun _ => rfl)
          (ψ : Rep.res f A →ₗ[k] Rep.res f B) (fun g a => hψ (f g) a) (locRes₂S S A f x) := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

end PushS

section Local

variable {p : ℕ} [Fact p.Prime]
  (M : Rep.{0} (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) [FiniteDimensional (ZMod p) M]
  (hsm : ∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s ∈ F.fixingSubgroup, M.ρ s m = m)

include hsm in

lemma exists_uniform_level : ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
    ∀ s ∈ F.fixingSubgroup, ∀ m : M, M.ρ s m = m := by
  classical
  let b := Module.finBasis (ZMod p) M
  choose F hF using hsm
  refine ⟨⨆ i, F (b i), ?_, fun s hs m => ?_⟩
  · haveI : ∀ i, FiniteDimensional ℚ (F (b i)) := fun i => (hF (b i)).1
    exact IntermediateField.finiteDimensional_iSup_of_finite
  · have hfix : ∀ i, M.ρ s (b i) = b i := fun i =>
      (hF (b i)).2 s (IntermediateField.fixingSubgroup_antitone (le_iSup (fun i => F (b i)) i) hs)
    have : M.ρ s = LinearMap.id := b.ext fun i => by simpa using hfix i
    simp [this]

lemma exists_level_cycloChar : ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
    ∀ s ∈ F.fixingSubgroup, ((cycloChar p s : (ZMod p)ˣ) : ZMod p) = 1 := by
  obtain ⟨F, hF, h⟩ := exists_level_ofChar_cycloChar_comp (p := p)
    (MonoidHom.id (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (1 : ZMod p)
  refine ⟨F, hF, fun s hs => ?_⟩
  have := h s hs
  simpa [Representation.twist_apply_apply] using this

variable (q : Nat.Primes) [Fact ((q : ℕ)).Prime]

local notation "rq" => primeLocalToGlobal q

abbrev D₁ : Rep (ZMod p) (primeLocalGaloisGroup q) := Rep.res rq (M.dualTwist (cycloChar p))

abbrev D₂ : Rep (ZMod p) (primeLocalGaloisGroup q) := (Rep.res rq M).dualTwist ((cycloChar p).comp rq)

abbrev Nq (p : ℕ) [Fact p.Prime] (q : Nat.Primes) : Rep (ZMod p) (primeLocalGaloisGroup q) :=
  ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))

omit [FiniteDimensional (ZMod p) M] [Fact ((q : ℕ)).Prime] in
lemma D₁_ρ_eq_D₂_ρ : (D₁ M q).ρ = (D₂ M q).ρ := by
  ext g f m
  simp [Representation.twist_apply_apply]

omit [FiniteDimensional (ZMod p) M] [Fact ((q : ℕ)).Prime] in
lemma D₁_invariants_eq : (D₁ M q).ρ.invariants = (D₂ M q).ρ.invariants := by
  rw [D₁_ρ_eq_D₂_ρ]

omit [FiniteDimensional (ZMod p) M] [Fact ((q : ℕ)).Prime] in

lemma apply_ρ_of_mem_invariants (d : (D₁ M q).ρ.invariants) (g : primeLocalGaloisGroup q) (m : M) :
    (d : Dual (ZMod p) M) (M.ρ (rq g) m) = ((cycloChar p (rq g) : (ZMod p)ˣ) : ZMod p) * (d : Dual (ZMod p) M) m := by
  have h := d.2 g

  have h' := congrArg (fun f : Dual (ZMod p) M => f (M.ρ (rq g) m)) h
  simp only at h'
  rw [← h']
  simp [Representation.twist_apply_apply, Module.Dual.transpose_apply, Representation.inv_self_apply]

abbrev dLin (d : (D₁ M q).ρ.invariants) : Rep.res rq M →ₗ[ZMod p] Nq p q :=
  (d : Dual (ZMod p) M)

omit [FiniteDimensional (ZMod p) M] [Fact ((q : ℕ)).Prime] in
lemma dLin_equivariant (d : (D₁ M q).ρ.invariants) (g : primeLocalGaloisGroup q) (a : Rep.res rq M) :
    dLin M q d ((Rep.res rq M).ρ g a) = (Nq p q).ρ g (dLin M q d a) := by
  change (d : Dual (ZMod p) M) (M.ρ (rq g) a) = _
  rw [apply_ρ_of_mem_invariants]
  simp [Representation.twist_apply_apply]

def pairCocycle (z : ↥(levelCocycles₂ rq (Rep.res rq M))) (d : (D₁ M q).ρ.invariants) :
    ↥(levelCocycles₂ rq (Nq p q)) :=
  (levelCocycles₂Map (rH := rq) (rG := rq) (A := Rep.res rq M) (B := Nq p q)
    (MonoidHom.id (primeLocalGaloisGroup q)) (fun _ => rfl) (dLin M q d) (dLin_equivariant M q d)) z

omit [FiniteDimensional (ZMod p) M] [Fact ((q : ℕ)).Prime] in
@[scoped simp] lemma pairCocycle_apply (z : ↥(levelCocycles₂ rq (Rep.res rq M))) (d : (D₁ M q).ρ.invariants)
    (g : primeLocalGaloisGroup q × primeLocalGaloisGroup q) :
    (pairCocycle M q z d).1 g = (d : Dual (ZMod p) M) (z.1 g) := rfl

omit [FiniteDimensional (ZMod p) M] [Fact ((q : ℕ)).Prime] in

lemma theta2_mk_apply
    (inv : continuousH2 rq (Nq p q) →ₗ[ZMod p] ZMod p)
    (θ : continuousH2 rq (Rep.res rq M) →ₗ[ZMod p] Dual (ZMod p) (D₁ M q).ρ.invariants)
    (hθ : IsTheta2 rq (Module.Dual.eval (ZMod p) M : Rep.res rq M →ₗ[ZMod p] D₁ M q →ₗ[ZMod p] Nq p q) inv θ)
    (z : ↥(levelCocycles₂ rq (Rep.res rq M))) (d : (D₁ M q).ρ.invariants) :
    θ (continuousH2π rq (Rep.res rq M) z) d = inv (continuousH2π rq (Nq p q) (pairCocycle M q z d)) :=
  hθ z d (pairCocycle M q z d) (fun _ => rfl)

omit [FiniteDimensional (ZMod p) M] [Fact ((q : ℕ)).Prime] in

lemma theta2_unique
    (inv : continuousH2 rq (Nq p q) →ₗ[ZMod p] ZMod p)
    (θ θ' : continuousH2 rq (Rep.res rq M) →ₗ[ZMod p] Dual (ZMod p) (D₁ M q).ρ.invariants)
    (hθ : IsTheta2 rq (Module.Dual.eval (ZMod p) M : Rep.res rq M →ₗ[ZMod p] D₁ M q →ₗ[ZMod p] Nq p q) inv θ)
    (hθ' : IsTheta2 rq (Module.Dual.eval (ZMod p) M : Rep.res rq M →ₗ[ZMod p] D₁ M q →ₗ[ZMod p] Nq p q) inv θ') :
    θ = θ' := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  refine LinearMap.ext fun d => ?_
  change θ (continuousH2π rq _ z) d = θ' (continuousH2π rq _ z) d
  rw [theta2_mk_apply M q inv θ hθ, theta2_mk_apply M q inv θ' hθ']

include hsm in
omit [FiniteDimensional (ZMod p) M] [Fact ((q : ℕ)).Prime] in

lemma hsm_res : ∀ m : Rep.res rq M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
    ∀ s, rq s ∈ F.fixingSubgroup → (Rep.res rq M).ρ s m = m :=
  fun m => let ⟨F, hF, h⟩ := hsm m; ⟨F, hF, fun s hs => h (rq s) hs⟩

include hsm in
omit [Fact ((q : ℕ)).Prime] in

lemma hsm_D₂ : ∀ x : D₂ M q, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
    ∀ s, rq s ∈ F.fixingSubgroup → (D₂ M q).ρ s x = x := by
  obtain ⟨F₀, hF₀, h₀⟩ := exists_uniform_level M hsm
  obtain ⟨F₁, hF₁, h₁⟩ := exists_level_cycloChar (p := p)
  haveI := hF₀; haveI := hF₁
  refine fun x => ⟨F₀ ⊔ F₁, IntermediateField.finiteDimensional_sup F₀ F₁, fun s hs => ?_⟩
  have hs₀ : rq s ∈ F₀.fixingSubgroup := IntermediateField.fixingSubgroup_antitone le_sup_left hs
  have hs₁ : rq s ∈ F₁.fixingSubgroup := IntermediateField.fixingSubgroup_antitone le_sup_right hs
  have hinv : ∀ m, M.ρ (rq s)⁻¹ m = m := fun m => h₀ _ (inv_mem hs₀) m
  refine LinearMap.ext fun m => ?_
  simp [Representation.twist_apply_apply, Module.Dual.transpose_apply, hinv, h₁ _ hs₁]

omit [FiniteDimensional (ZMod p) M] [Fact ((q : ℕ)).Prime] in

lemma eval_isEquivariantBilinear_D₂ :
    Rep.IsEquivariantBilinear (Rep.res rq M) (D₂ M q) (Nq p q)
      (Module.Dual.eval (ZMod p) M : Rep.res rq M →ₗ[ZMod p] D₂ M q →ₗ[ZMod p] Nq p q) := by
  intro g a b
  simp [Representation.twist_apply_apply, Module.Dual.transpose_apply, Representation.inv_self_apply]

include hsm in

theorem bijective_theta2 (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p)
    (θ : continuousH2 rq (Rep.res rq M) →ₗ[ZMod p] Dual (ZMod p) (D₁ M q).ρ.invariants)
    (hθ : IsTheta2 rq (Module.Dual.eval (ZMod p) M : Rep.res rq M →ₗ[ZMod p] D₁ M q →ₗ[ZMod p] Nq p q)
      (localInv p ζ q) θ) :
    Function.Bijective θ := by

  have hφ := eval_isEquivariantBilinear_D₂ M q
  obtain ⟨⟨θ₀, hθ₀⟩, ⟨θ₂, hθ₂⟩⟩ := exists_theta0_and_theta2 (M := Rep.res rq M) (D := D₂ M q) (N := Nq p q) rq
    (Module.Dual.eval (ZMod p) M : Rep.res rq M →ₗ[ZMod p] D₂ M q →ₗ[ZMod p] Nq p q) hφ (localInv p ζ q)
  obtain ⟨θ₁, hθ₁⟩ := exists_theta1 (M := Rep.res rq M) (D := D₂ M q) (N := Nq p q) rq
    (Module.Dual.eval (ZMod p) M : Rep.res rq M →ₗ[ZMod p] D₂ M q →ₗ[ZMod p] Nq p q) hφ (hsm_D₂ M hsm q)
    (localInv p ζ q)
  have hinv := (isLocalInv_localInv_and_bijective p ζ hζ q).2
  have hbij := (bijective_theta_dualTwist_of_primeLocal q (Rep.res rq M) (hsm_res M hsm q)
    (localInv p ζ q) hinv θ₀ hθ₀ θ₁ hθ₁ θ₂ hθ₂).2.2

  let e : (D₁ M q).ρ.invariants ≃ₗ[ZMod p] (D₂ M q).ρ.invariants :=
    LinearEquiv.ofEq _ _ (D₁_invariants_eq M q)
  let θ' : continuousH2 rq (Rep.res rq M) →ₗ[ZMod p] Dual (ZMod p) (D₁ M q).ρ.invariants :=
    e.dualMap.toLinearMap ∘ₗ θ₂
  have hθ' : IsTheta2 rq (Module.Dual.eval (ZMod p) M : Rep.res rq M →ₗ[ZMod p] D₁ M q →ₗ[ZMod p] Nq p q)
      (localInv p ζ q) θ' := by
    intro z d c hc
    exact hθ₂ z (e d) c hc
  have hθ'bij : Function.Bijective θ' := e.dualMap.bijective.comp hbij
  rwa [theta2_unique M q (localInv p ζ q) θ θ' hθ hθ']

end Local

section Global

variable {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes)
  (M : Rep.{0} (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) [FiniteDimensional (ZMod p) M]

abbrev NQ (p : ℕ) [Fact p.Prime] : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :=
  ofChar (k := ZMod p) (cycloChar p)

omit [FiniteDimensional (ZMod p) M] in

lemma apply_ρ_of_mem_invariants_global (d : (M.dualTwist (cycloChar p)).ρ.invariants)
    (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (m : M) :
    (d : Dual (ZMod p) M) (M.ρ g m) = ((cycloChar p g : (ZMod p)ˣ) : ZMod p) * (d : Dual (ZMod p) M) m := by
  have h' := congrArg (fun f : Dual (ZMod p) M => f (M.ρ g m)) (d.2 g)
  simp only at h'
  rw [← h']
  simp [Representation.twist_apply_apply, Module.Dual.transpose_apply, Representation.inv_self_apply]

omit [FiniteDimensional (ZMod p) M] in
lemma dGlob_equivariant (d : (M.dualTwist (cycloChar p)).ρ.invariants)
    (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (m : M) :
    ((d : Dual (ZMod p) M) : M →ₗ[ZMod p] NQ p) (M.ρ g m) = (NQ p).ρ g (((d : Dual (ZMod p) M) : M →ₗ[ZMod p] NQ p) m) := by
  rw [apply_ρ_of_mem_invariants_global]
  simp [Representation.twist_apply_apply]

abbrev dStar (d : (M.dualTwist (cycloChar p)).ρ.invariants) : continuousH2S S M →ₗ[ZMod p] continuousH2S S (NQ p) :=
  continuousH2SMap S ((d : Dual (ZMod p) M) : M →ₗ[ZMod p] NQ p) (dGlob_equivariant M d)

variable (q : ↥S)

def ιq (d : (M.dualTwist (cycloChar p)).ρ.invariants) : (D₁ M (q : Nat.Primes)).ρ.invariants :=
  ⟨(d : M.dualTwist (cycloChar p)), fun g => d.2 (extArithLoc S (Sum.inr q) g)⟩

def ιqLin : (M.dualTwist (cycloChar p)).ρ.invariants →ₗ[ZMod p] (D₁ M (q : Nat.Primes)).ρ.invariants where
  toFun := ιq S M q
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [FiniteDimensional (ZMod p) M] in
lemma ιqLin_injective : Function.Injective (ιqLin S M q) := by
  intro d d' h
  apply Subtype.ext
  exact congrArg (fun x : (D₁ M (q : Nat.Primes)).ρ.invariants => (x : Dual (ZMod p) M)) h

omit [FiniteDimensional (ZMod p) M] in

lemma theta2_locRes_apply (ζ : AlgebraicClosure ℚ)
    (θ : continuousH2 (extArithLoc S (Sum.inr q)) (Rep.res (extArithLoc S (Sum.inr q)) M) →ₗ[ZMod p]
        Module.Dual (ZMod p) (Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p))).ρ.invariants)
    (hθ : haveI : Fact (((q : Nat.Primes) : ℕ)).Prime := ⟨(q : Nat.Primes).prop⟩
      IsTheta2 (extArithLoc S (Sum.inr q))
        (Module.Dual.eval (ZMod p) M :
          Rep.res (extArithLoc S (Sum.inr q)) M →ₗ[ZMod p]
            Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p)) →ₗ[ZMod p]
              ofChar (k := ZMod p) ((cycloChar p).comp (extArithLoc S (Sum.inr q))))
        (localInv p ζ (q : Nat.Primes)) θ)
    (x : continuousH2S S M) (d : (M.dualTwist (cycloChar p)).ρ.invariants) :
    θ (locRes₂S S M (extArithLoc S (Sum.inr q)) x) (ιq S M q d)
      = (haveI : Fact (((q : Nat.Primes) : ℕ)).Prime := ⟨(q : Nat.Primes).prop⟩
         localInv p ζ (q : Nat.Primes) (locRes₂S S (NQ p) (extArithLoc S (Sum.inr q)) (dStar S M d x))) := by
  haveI : Fact (((q : Nat.Primes) : ℕ)).Prime := ⟨(q : Nat.Primes).prop⟩
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x

  have key := theta2_mk_apply M (q : Nat.Primes) (localInv p ζ (q : Nat.Primes)) θ hθ
    (levelCocycles₂Map (rH := MonoidHom.id _) (rG := extArithLoc S (Sum.inr q))
      (extArithLoc S (Sum.inr q)) (fun _ => rfl)
      (LinearMap.id : M →ₗ[ZMod p] Rep.res (extArithLoc S (Sum.inr q)) M) (fun _ _ => rfl)
      (levelCocyclesS₂ToLevelCocycles₂ S M c)) (ιq S M q d)
  exact key

omit [FiniteDimensional (ZMod p) M] in

lemma locRes_inl_dStar_eq_zero
    (hinf2 : Subsingleton (continuousH2 (extArithLoc S (Sum.inl ())) (Rep.res (extArithLoc S (Sum.inl ())) M)))
    (d : (M.dualTwist (cycloChar p)).ρ.invariants) (x : continuousH2S S M) :
    locRes₂S S (NQ p) (extArithLoc S (Sum.inl ())) (dStar S M d x) = 0 := by
  rw [dStar, locRes₂S_continuousH2SMap, Subsingleton.elim (locRes₂S S M (extArithLoc S (Sum.inl ())) x) 0,
    map_zero]

end Global

section Prod

variable {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes)
  (M : Rep.{0} (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))

def LocProd : Type :=
  ∀ q : ↥S, continuousH2 (extArithLoc S (Sum.inr q)) (Rep.res (extArithLoc S (Sum.inr q)) M)

scoped instance instAddCommGroupLocProd : AddCommGroup (LocProd S M) := Pi.addCommGroup

abbrev moduleLocProdRaw : Module (ZMod p)
    (∀ q : ↥S, continuousH2 (extArithLoc S (Sum.inr q)) (Rep.res (extArithLoc S (Sum.inr q)) M)) :=
  inferInstance

scoped instance instModuleLocProd : Module (ZMod p) (LocProd S M) := moduleLocProdRaw S M

def locPi : continuousH2S S M →ₗ[ZMod p] LocProd S M :=
  (LinearMap.pi fun q : ↥S => locRes₂S S M (extArithLoc S (Sum.inr q)) :
    continuousH2S S M →ₗ[ZMod p]
      ∀ q : ↥S, continuousH2 (extArithLoc S (Sum.inr q)) (Rep.res (extArithLoc S (Sum.inr q)) M))

@[scoped simp] lemma locPi_apply (x : continuousH2S S M) (q : ↥S) :
    locPi S M x q = locRes₂S S M (extArithLoc S (Sum.inr q)) x := rfl

def projq (q : ↥S) : LocProd S M →ₗ[ZMod p]
    continuousH2 (extArithLoc S (Sum.inr q)) (Rep.res (extArithLoc S (Sum.inr q)) M) where
  toFun z := z q
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[scoped simp] lemma projq_apply (q : ↥S) (z : LocProd S M) : projq S M q z = z q := rfl

variable [FiniteDimensional (ZMod p) M]
  (θ₂ : ∀ q : ↥S,
      continuousH2 (extArithLoc S (Sum.inr q)) (Rep.res (extArithLoc S (Sum.inr q)) M) →ₗ[ZMod p]
        Module.Dual (ZMod p) (Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p))).ρ.invariants)

def Lam : LocProd S M →ₗ[ZMod p] Module.Dual (ZMod p) (M.dualTwist (cycloChar p)).ρ.invariants :=
  ∑ q : ↥S, (ιqLin S M q).dualMap ∘ₗ θ₂ q ∘ₗ projq S M q

omit [FiniteDimensional (ZMod p) M] in
lemma Lam_apply (z : LocProd S M) (d : (M.dualTwist (cycloChar p)).ρ.invariants) :
    Lam S M θ₂ z d = ∑ q : ↥S, θ₂ q (z q) (ιq S M q d) := by
  simp only [Lam, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.dualMap_apply]
  rfl

end Prod

section Assembly

variable {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
  (M : Rep.{0} (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) [FiniteDimensional (ZMod p) M]
  (hsm : ∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s ∈ F.fixingSubgroup, M.ρ s m = m)
  (hMur : ∀ q : Nat.Primes, q ∉ S → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
      A.LiesOverPrime (q : ℕ) → ∀ g ∈ A.inertiaSubgroupIn ℚ, M.ρ g = 1)
  (hinf2 : Subsingleton (continuousH2 (extArithLoc S (Sum.inl ())) (Rep.res (extArithLoc S (Sum.inl ())) M)))
  (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p)
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
        (localInv p ζ (q : Nat.Primes)) (θ₂ q))

include hsm hζ hθ₂ in

lemma bijective_theta2_at (q : ↥S) : Function.Bijective (θ₂ q) := by
  haveI : Fact (((q : Nat.Primes) : ℕ)).Prime := ⟨(q : Nat.Primes).prop⟩
  exact bijective_theta2 M hsm (q : Nat.Primes) ζ hζ (θ₂ q) (hθ₂ q)

include hζ hθ₂ in
omit [FiniteDimensional (ZMod p) M] in

lemma Lam_locPi_eq_zero (hp2 : p ≠ 2) (hinf2 : Subsingleton (continuousH2 (extArithLoc S (Sum.inl ()))
      (Rep.res (extArithLoc S (Sum.inl ())) M)))
    (x : continuousH2S S M) : Lam S M θ₂ (locPi S M x) = 0 := by
  refine LinearMap.ext fun d => ?_
  rw [Lam_apply, LinearMap.zero_apply]
  have hrecip := sum_localInv_locRes2S_eq_zero_of_ne_two S hp2 ζ hζ (dStar S M d x)
    (locRes_inl_dStar_eq_zero S M hinf2 d x)
  refine Eq.trans (Finset.sum_congr rfl fun q _ => ?_) hrecip
  exact theta2_locRes_apply S M q ζ (θ₂ q) (hθ₂ q) x d

include hsm hζ hθ₂ hpS in

lemma Lam_surjective : Function.Surjective (Lam S M θ₂) := by
  classical
  intro φ
  set q₀ : ↥S := ⟨pPrime p, hpS⟩

  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (ιqLin S M q₀)
    (LinearMap.ker_eq_bot.2 (ιqLin_injective S M q₀))
  obtain ⟨w, hw⟩ := (bijective_theta2_at S M hsm ζ hζ θ₂ hθ₂ q₀).2 (φ ∘ₗ g)
  refine ⟨Pi.single q₀ w, LinearMap.ext fun d => ?_⟩
  rw [Lam_apply, Finset.sum_eq_single q₀]
  · change θ₂ q₀ ((Pi.single q₀ w : LocProd S M) q₀) (ιqLin S M q₀ d) = φ d
    rw [Pi.single_eq_same, hw, LinearMap.comp_apply]
    have hgd := LinearMap.congr_fun hg d
    rw [LinearMap.comp_apply, LinearMap.id_apply] at hgd
    exact congrArg φ hgd
  · intro q _ hq
    change θ₂ q ((Pi.single q₀ w : LocProd S M) q) (ιq S M q d) = 0
    rw [Pi.single_eq_of_ne hq, map_zero, LinearMap.zero_apply]
  · intro h; exact absurd (Finset.mem_univ q₀) h

include hsm hζ hθ₂ in

lemma finite_locProd : Module.Finite (ZMod p) (LocProd S M) := by
  have hq : ∀ q : ↥S, Module.Finite (ZMod p)
      (continuousH2 (extArithLoc S (Sum.inr q)) (Rep.res (extArithLoc S (Sum.inr q)) M)) := fun q =>
    Module.Finite.of_injective (θ₂ q) (bijective_theta2_at S M hsm ζ hζ θ₂ hθ₂ q).1
  exact (Module.Finite.pi : Module.Finite (ZMod p)
    (∀ q : ↥S, continuousH2 (extArithLoc S (Sum.inr q)) (Rep.res (extArithLoc S (Sum.inr q)) M)))

include hpS hsm hMur hζ hθ₂ in

lemma ker_Lam_eq_range (hp2 : p ≠ 2) (hinf2 : Subsingleton (continuousH2 (extArithLoc S (Sum.inl ()))
      (Rep.res (extArithLoc S (Sum.inl ())) M))) :
    LinearMap.ker (Lam S M θ₂) = LinearMap.range (locPi S M) := by
  haveI := finite_locProd S M hsm ζ hζ θ₂ hθ₂

  obtain ⟨W, hWfin, hWle, hWsup⟩ :=
    exists_range_locRes_continuousH2S_sup_eq_top_finrank_le_finrank_invariants_dualTwist_of_ne_two S hp2 hpS M hsm hMur hinf2
  let W' : Submodule (ZMod p) (LocProd S M) := W
  haveI : Module.Finite (ZMod p) W' := hWfin
  have hWle' : Module.finrank (ZMod p) W' ≤ Module.finrank (ZMod p) (M.dualTwist (cycloChar p)).ρ.invariants :=
    hWle
  have hWsup' : LinearMap.range (locPi S M) ⊔ W' = ⊤ := hWsup

  have hle : LinearMap.range (locPi S M) ≤ LinearMap.ker (Lam S M θ₂) := by
    rintro _ ⟨x, rfl⟩
    exact Lam_locPi_eq_zero S M ζ hζ θ₂ hθ₂ hp2 hinf2 x

  have hsurj := Lam_surjective S hpS M hsm ζ hζ θ₂ hθ₂
  have h1 := LinearMap.finrank_range_add_finrank_ker (Lam S M θ₂)
  rw [LinearMap.range_eq_top.2 hsurj, finrank_top] at h1
  have h2 : Module.finrank (ZMod p) (Module.Dual (ZMod p) (M.dualTwist (cycloChar p)).ρ.invariants)
      = Module.finrank (ZMod p) (M.dualTwist (cycloChar p)).ρ.invariants := Subspace.dual_finrank_eq
  have h3 : Module.finrank (ZMod p) (LocProd S M)
      ≤ Module.finrank (ZMod p) (LinearMap.range (locPi S M)) + Module.finrank (ZMod p) W' := by
    rw [← finrank_top (R := ZMod p) (M := LocProd S M), ← hWsup']
    exact Submodule.finrank_add_le_finrank_add_finrank _ _
  symm
  refine Submodule.eq_of_le_of_finrank_le hle ?_
  omega

end Assembly

end P2M9ca
p2m_reactivate "P2MW.S_groupCohomology_exists_continuousH2S_locRes_eq_iff_and_surjective_sum_theta2_of_ne_two.P2M9ca"

theorem solution
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    [FiniteDimensional (ZMod p) M]
    (hsm : ∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s ∈ F.fixingSubgroup, M.ρ s m = m)
    (hMur : ∀ q : Nat.Primes, q ∉ S → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
      A.LiesOverPrime (q : ℕ) → ∀ g ∈ A.inertiaSubgroupIn ℚ, M.ρ g = 1)
    (hinf2 : Subsingleton (continuousH2 (extArithLoc S (Sum.inl ())) (Rep.res (extArithLoc S (Sum.inl ())) M)))
    (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p)
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
          ∑ q : ↥S, θ₂ q (z q) ⟨(d : M.dualTwist (cycloChar p)), fun g => d.2 (extArithLoc S (Sum.inr q) g)⟩ = φ d) := by
  have hker := P2M9ca.ker_Lam_eq_range S hpS M hsm hMur ζ hζ θ₂ hθ₂ hp2 hinf2
  refine ⟨fun z => ?_, fun φ => ?_⟩
  ·
    have hiff : (∃ x : continuousH2S S M, ∀ q : ↥S, locRes₂S S M (extArithLoc S (Sum.inr q)) x = z q) ↔
        (z : P2M9ca.LocProd S M) ∈ LinearMap.ker (P2M9ca.Lam S M θ₂) := by
      rw [hker]
      constructor
      · rintro ⟨x, hx⟩; exact ⟨x, funext hx⟩
      · rintro ⟨x, hx⟩; exact ⟨x, fun q => congrFun hx q⟩
    rw [hiff]
    change P2M9ca.Lam S M θ₂ z = 0 ↔ _
    refine ⟨fun h d => ?_, fun h => LinearMap.ext fun d => ?_⟩
    · have := LinearMap.congr_fun h d
      rw [P2M9ca.Lam_apply, LinearMap.zero_apply] at this
      exact this
    · rw [P2M9ca.Lam_apply, LinearMap.zero_apply]
      exact h d
  ·
    obtain ⟨z, hz⟩ := P2M9ca.Lam_surjective S hpS M hsm ζ hζ θ₂ hθ₂ φ
    refine ⟨z, fun d => ?_⟩
    have := LinearMap.congr_fun hz d
    rw [P2M9ca.Lam_apply] at this
    exact this

end
p2m_reactivate "P2MW.S_groupCohomology_exists_continuousH2S_locRes_eq_iff_and_surjective_sum_theta2_of_ne_two.P2M9ca"

end S_groupCohomology_exists_continuousH2S_locRes_eq_iff_and_surjective_sum_theta2_of_ne_two
end P2MW
export P2MW.S_groupCohomology_exists_continuousH2S_locRes_eq_iff_and_surjective_sum_theta2_of_ne_two (solution)
