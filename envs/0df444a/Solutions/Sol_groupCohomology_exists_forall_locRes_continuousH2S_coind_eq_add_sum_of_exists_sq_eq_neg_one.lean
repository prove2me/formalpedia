-- Prove2me | solution 1 for groupCohomology.exists_forall_locRes_continuousH2S_coind_eq_add_sum_of_exists_sq_eq_neg_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/53080a3e-edf3-5a1d-a972-e4fc0646a504

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_LevelSubgroup
import Theorems.Thm_TWNum_subsingleton_continuousH2_extArithLoc_inl
import Theorems.Thm_groupCohomology_exists_forall_locRes_continuousH2S_coind_trivial_eq_add_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_exists_forall_locRes_continuousH2S_coind_eq_add_sum_of_exists_sq_eq_neg_one
p2m_attr_erase "instance" "AlgebraicClosure.Rat.isGalois groupCohomology.instMulDistribMulActionGaloisSUnits NumberField.LevelArith.instCommGroupUnitsModPow IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap"
p2m_attr_erase "instance" "RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion NumberField.AdelicHaar.locallyCompactSpace_adeleRing NumberField.AdelicHaar.finite_residueField_adicCompletionIntegers NumberField.AdelicHaar.locallyCompactSpace_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_finiteAdeleRing NumberField.AdelicHaar.compactSpace_adicCompletionIntegers NumberField.AdelicHaar.t2Space_finiteAdeleRing NumberField.AdelicHaar.t2Space_matrix_adeleRing NumberField.AdelicHaar.t2Space_adeleRing NumberField.AdelicHaar.fact_isOpen_adicCompletionIntegers NumberField.AdelicHaar.t2Space_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_matrix_adeleRing NumberField.AdelicHaar.t2Space_infiniteAdeleRing NumberField.AdelicHaar.properSpace_adicCompletion M4aHerbrand.Bridge.instT2SpaceAdeleRing M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite Deep.NTSupply.instNormalRayClassSubgroup instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO"
p2m_attr_erase "instance" "ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal groupCohomology.Kummer.instMulDistribMulActionRootsOfUnity LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal"
p2m_attr_erase "simp" "groupCohomology.coe_continuousH1SrMap_apply groupCohomology.continuousH2SrMap_continuousH2Srπ groupCohomology.coe_levelCocyclesSr₂Map groupCohomology.coe_smul_galoisSUnits groupCohomology.galoisSUnitsToUnits_apply NumberField.LevelArith.coe_levelFieldEquiv NumberField.LevelArith.modP_apply_mk NumberField.LevelArith.coe_levelFieldEquiv_symm NumberField.LevelArith.torsionP_apply_coe NumberField.LevelArith.repTorsionPMap_hom_apply_coe NumberField.LevelArith.toZMod_apply NumberField.LevelArith.repModPMap_hom_mk NumberField.SUnits.val_zsmul NumberField.SUnits.val_add NumberField.LevelArith.smul_mk NumberField.LevelArith.selmerRepInt_ρ_apply NumberField.LevelArith.selmerRepField_ρ_apply NumberField.LevelArith.unitsModPowMap_mk NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq groupCohomology.continuousH2Inflation_H2π groupCohomology.levelInflate₂_apply groupCohomology.coe_levelInflateCocycles₂ groupCohomology.levelInflate₁_apply SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply"
p2m_attr_erase "simp" "LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd"
p2m_attr_erase "simp" "M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq M4aHerbrand.Bridge.finiteConorm_apply M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply"
p2m_attr_erase "simp" "Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk M4aHerbrand.IdeleGaloisDescent.classAct_mk Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent IsLocalRing.principalUnits_zero ExtCitation.LocalLevel.coe_smul_OO"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply groupCohomology.Kummer.coe_kummerCocycleRoots groupCohomology.Kummer.mem_powerSubgroup_iff groupCohomology.Kummer.val_smul_units groupCohomology.Kummer.kummerHom_apply groupCohomology.Kummer.coe_smul_rootsOfUnity groupCohomology.unitsInflate₁_apply groupCohomology.unitsInflate₂_apply AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open CategoryTheory Module groupCohomology ExtCitation

noncomputable section
namespace P2Mb58

local notation "Γ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

section FreeSection

variable {H : Type} [Group H] (r : H →* Γ) (U : Subgroup Γ)
  (hfree : ∀ (γ : Γ) (h : H), γ * r h * γ⁻¹ ∈ U → h = 1)

def rep (γ : Γ) : Γ := (DoubleCoset.mk U r.range γ : DoubleCoset.Quotient (U : Set Γ) r.range).out

lemma rep_spec (γ : Γ) : ∃ u ∈ U, ∃ h : H, rep r U γ = u * γ * r h := by
  obtain ⟨u, k, hu, hk, h⟩ := DoubleCoset.mk_out_eq_mul U r.range γ
  obtain ⟨h0, rfl⟩ := hk
  exact ⟨u, hu, h0, h⟩

lemma rep_eq_of_rel {γ γ' : Γ} (h : ∃ u ∈ U, ∃ h : H, γ' = u * γ * r h) : rep r U γ' = rep r U γ := by
  obtain ⟨u, hu, h0, rfl⟩ := h
  unfold rep
  congr 1
  exact ((DoubleCoset.eq U r.range γ _).2 ⟨u, hu, r h0, ⟨h0, rfl⟩, rfl⟩).symm

lemma exists_dec (γ : Γ) : ∃ h : H, ∃ u ∈ U, γ = u * rep r U γ * r h := by
  obtain ⟨u, hu, h0, h⟩ := rep_spec r U γ
  refine ⟨h0⁻¹, u⁻¹, inv_mem hu, ?_⟩
  rw [h, map_inv]
  group

def hsec (γ : Γ) : H := (exists_dec r U γ).choose

lemma hsec_spec (γ : Γ) : ∃ u ∈ U, γ = u * rep r U γ * r (hsec r U γ) := (exists_dec r U γ).choose_spec

include hfree in

lemma dec_unique {ρ u u' : Γ} (hu : u ∈ U) (hu' : u' ∈ U) {h h' : H}
    (e : u * ρ * r h = u' * ρ * r h') : h = h' := by
  have e2 : u'⁻¹ * u * ρ = ρ * r h' * (r h)⁻¹ := by
    calc u'⁻¹ * u * ρ = u'⁻¹ * (u * ρ * r h) * (r h)⁻¹ := by group
      _ = u'⁻¹ * (u' * ρ * r h') * (r h)⁻¹ := by rw [e]
      _ = ρ * r h' * (r h)⁻¹ := by group
  have key : ρ * r (h' * h⁻¹) * ρ⁻¹ = u'⁻¹ * u := by
    rw [map_mul, map_inv]
    calc ρ * (r h' * (r h)⁻¹) * ρ⁻¹ = (ρ * r h' * (r h)⁻¹) * ρ⁻¹ := by group
      _ = (u'⁻¹ * u * ρ) * ρ⁻¹ := by rw [e2]
      _ = u'⁻¹ * u := by group
  have hmem : ρ * r (h' * h⁻¹) * ρ⁻¹ ∈ U := by
    rw [key]; exact mul_mem (inv_mem hu') hu
  have := hfree _ _ hmem
  rw [mul_inv_eq_one] at this
  exact this.symm

include hfree in
lemma hsec_mul (γ : Γ) (g : H) : hsec r U (γ * r g) = hsec r U γ * g := by
  obtain ⟨u, hu, e⟩ := hsec_spec r U (γ * r g)
  obtain ⟨u', hu', e'⟩ := hsec_spec r U γ
  have hrep : rep r U (γ * r g) = rep r U γ := rep_eq_of_rel r U ⟨1, one_mem U, g, by rw [one_mul]⟩
  rw [hrep] at e
  refine dec_unique r U hfree (ρ := rep r U γ) hu hu' ?_
  rw [← e, map_mul, ← mul_assoc, ← e']

include hfree in
lemma hsec_umul (γ : Γ) {u : Γ} (hu : u ∈ U) : hsec r U (u * γ) = hsec r U γ := by
  obtain ⟨u₁, hu₁, e⟩ := hsec_spec r U (u * γ)
  obtain ⟨u', hu', e'⟩ := hsec_spec r U γ
  have hrep : rep r U (u * γ) = rep r U γ := rep_eq_of_rel r U ⟨u, hu, 1, by rw [map_one, mul_one]⟩
  rw [hrep] at e
  refine dec_unique r U hfree (ρ := rep r U γ) hu₁ (mul_mem hu hu') ?_
  rw [← e]
  calc u * γ = u * (u' * rep r U γ * r (hsec r U γ)) := congrArg (u * ·) e'
    _ = u * u' * rep r U γ * r (hsec r U γ) := by group

end FreeSection

section Coind

variable {k : Type} [CommRing k] {H : Type} [Group H] (r : H →* Γ) (U : Subgroup Γ) (N : Rep k ↥U)

abbrev M : Rep k H := Rep.res r (Rep.coind U.subtype N)

lemma coind_apply_umul (f : M r U N) (u : ↥U) (x : Γ) : (f : Γ → N) ((u : Γ) * x) = N.ρ u ((f : Γ → N) x) :=
  f.2 u x

lemma M_ρ_apply (g : H) (f : M r U N) (x : Γ) : ((M r U N).ρ g f : Γ → N) x = (f : Γ → N) (x * r g) := rfl

variable (hfree : ∀ (γ : Γ) (h : H), γ * r h * γ⁻¹ ∈ U → h = 1)

def contract₁Fun (f : H → M r U N) (x : Γ) : N :=
  (f (hsec r U x) : Γ → N) (x * (r (hsec r U x))⁻¹)

include hfree in
lemma contract₁Fun_umul (f : H → M r U N) (u : ↥U) (x : Γ) :
    contract₁Fun r U N f ((u : Γ) * x) = N.ρ u (contract₁Fun r U N f x) := by
  unfold contract₁Fun
  rw [hsec_umul r U hfree x u.2, mul_assoc]
  exact coind_apply_umul r U N _ u _

def contract₁ (f : H → M r U N) : M r U N :=
  ⟨contract₁Fun r U N f, fun u x => contract₁Fun_umul r U N hfree f u x⟩

lemma contract₁_apply (f : H → M r U N) (x : Γ) :
    (contract₁ r U N hfree f : Γ → N) x = (f (hsec r U x) : Γ → N) (x * (r (hsec r U x))⁻¹) := rfl

include hfree in

theorem mem_coboundaries₁_of_free (f : cocycles₁ (M r U N)) : (f : H → M r U N) ∈ coboundaries₁ (M r U N) := by
  refine ⟨contract₁ r U N hfree f, ?_⟩
  funext g
  rw [d₀₁_hom_apply]
  apply Subtype.ext
  funext x
  set h : H := hsec r U x with hh
  set y : Γ := x * (r h)⁻¹ with hy
  have hyx : y * r h = x := inv_mul_cancel_right x _
  have hc := (mem_cocycles₁_iff (f : H → M r U N)).1 f.2 h g

  have hcy : (f (h * g) : Γ → N) y = (f g : Γ → N) x + (f h : Γ → N) y := by
    have := congrArg (fun m : M r U N => (m : Γ → N) y) hc
    have h1 : (((M r U N).ρ h (f g) : M r U N) : Γ → N) y = (f g : Γ → N) x := by
      rw [M_ρ_apply, hyx]
    simpa only [Submodule.coe_add, Pi.add_apply, h1] using this
  change ((contract₁ r U N hfree f : Γ → N) (x * r g)) - (contract₁ r U N hfree f : Γ → N) x = (f g : Γ → N) x
  rw [contract₁_apply, contract₁_apply, hsec_mul r U hfree, ← hh, r.map_mul]
  have e : x * r g * (r h * r g)⁻¹ = y := by rw [hy]; group
  rw [e, hcy, ← hy, add_sub_cancel_right]

include hfree in
theorem subsingleton_H1_of_free : Subsingleton (H1 (M r U N)) := by
  refine ⟨fun a b => ?_⟩
  induction a using H1_induction_on with
  | h a =>
  induction b using H1_induction_on with
  | h b =>
  rw [← sub_eq_zero, ← map_sub, H1π_eq_zero_iff]
  exact mem_coboundaries₁_of_free r U N hfree (a - b)

end Coind

section ArchFree

variable {p : ℕ} [Fact p.Prime]

lemma coe_eq_one_or_eq_cc (h : ↥archimedeanDecomposition) :
    (h : Γ) = 1 ∨ (h : Γ) = complexConjugation := by
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 h.2
  have h2 : complexConjugation ^ (2 : ℤ) = 1 := by
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, complexConjugation_sq]
  have hn' : (h : Γ) = complexConjugation ^ (n % 2) := by
    rw [← hn]
    conv_lhs => rw [← Int.emod_add_mul_ediv n 2, zpow_add, zpow_mul, h2, one_zpow, mul_one]
  rcases Int.emod_two_eq_zero_or_one n with h0 | h1
  · left; rw [hn', h0, zpow_zero]
  · right; rw [hn', h1, zpow_one]

lemma cc_apply_of_sq_eq_neg_one {j : AlgebraicClosure ℚ} (hj : j ^ 2 = -1) : complexConjugation j = -j := by
  apply complexEmbedding.toRingHom.injective
  change complexEmbedding (complexConjugation j) = complexEmbedding (-j)
  rw [complexEmbedding_complexConjugation, map_neg]
  set w : ℂ := complexEmbedding j with hw
  have hw2 : w ^ 2 = -1 := by rw [hw, ← map_pow, hj, map_neg, map_one]
  have hre : w.re * w.re - w.im * w.im = -1 := by
    have := congrArg Complex.re hw2
    simpa [sq, Complex.mul_re] using this
  have him : w.re * w.im = 0 := by
    have := congrArg Complex.im hw2
    simp only [sq, Complex.mul_im, Complex.neg_im, Complex.one_im, neg_zero] at this
    linarith
  have hre0 : w.re = 0 := by
    rcases mul_eq_zero.1 him with h | h
    · exact h
    · exfalso
      rw [h, mul_zero, sub_zero] at hre
      nlinarith [mul_self_nonneg w.re]
  apply Complex.ext
  · simp [hre0]
  · simp

lemma cc_apply_ne_of_isPrimitiveRoot (hp2 : p ≠ 2) {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ p) :
    complexConjugation ζ ≠ ζ := by
  intro h
  have hp : p.Prime := Fact.out
  have hemb : starRingEnd ℂ (complexEmbedding ζ) = complexEmbedding ζ := by
    rw [← complexEmbedding_complexConjugation, h]
  set z : ℂ := complexEmbedding ζ with hz
  have hζ' : IsPrimitiveRoot z p := hζ.map_of_injective complexEmbedding.toRingHom.injective
  have hzre : (z.re : ℂ) = z := Complex.conj_eq_iff_re.1 hemb
  have hpow : z.re ^ p = 1 := by
    apply Complex.ofReal_injective
    rw [Complex.ofReal_pow, hzre, hζ'.pow_eq_one, Complex.ofReal_one]
  have habs : |z.re| = 1 := by
    have : |z.re| ^ p = 1 := by rw [← abs_pow, hpow, abs_one]
    exact (pow_eq_one_iff_of_nonneg (abs_nonneg _) hp.ne_zero).1 this
  have hre2 : z.re ^ 2 = 1 := by
    rcases (abs_eq zero_le_one).1 habs with h | h <;> rw [h] <;> norm_num
  have hsq : z ^ 2 = 1 := by
    rw [← hzre, ← Complex.ofReal_pow, hre2, Complex.ofReal_one]
  have hdvd : p ∣ 2 := (hζ'.pow_eq_one_iff_dvd 2).1 hsq
  have : p ≤ 2 := Nat.le_of_dvd two_pos hdvd
  interval_cases p
  · exact Nat.not_prime_zero hp
  · exact Nat.not_prime_one hp
  · exact hp2 rfl

variable (F : IntermediateField ℚ (AlgebraicClosure ℚ))
  (h4 : p = 2 → ∃ i ∈ F, i ^ 2 = -1)
  (hFζ : ∀ s ∈ F.fixingSubgroup, cycloChar p s = 1)

include h4 hFζ in

lemma conj_cc_not_mem (γ : Γ) : γ * complexConjugation * γ⁻¹ ∉ F.fixingSubgroup := by
  intro hmem
  have hp : p.Prime := Fact.out
  by_cases hp2 : p = 2
  · obtain ⟨i, hiF, hi⟩ := h4 hp2
    have hfix : (γ * complexConjugation * γ⁻¹) i = i :=
      (IntermediateField.mem_fixingSubgroup_iff (K := F) _).1 hmem i hiF
    have hj : (γ⁻¹ i) ^ 2 = -1 := by rw [← map_pow, hi, map_neg, map_one]
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, cc_apply_of_sq_eq_neg_one hj, map_neg] at hfix
    have hγ : γ (γ⁻¹ i) = i := by rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
    rw [hγ] at hfix
    have hi0 : i = 0 := by
      have : i + i = 0 := by nth_rewrite 1 [← hfix]; exact neg_add_cancel i
      exact add_self_eq_zero.1 this
    rw [hi0] at hi
    norm_num at hi
  ·
    have hχ : cycloChar p complexConjugation = 1 := by
      have := hFζ _ hmem
      rwa [map_mul, map_mul, map_inv, mul_inv_cancel_comm] at this
    haveI : NeZero (p : ℚ) := ⟨Nat.cast_ne_zero.2 hp.ne_zero⟩
    haveI : NeZero p := ⟨hp.ne_zero⟩
    haveI : Fact (1 < p) := ⟨hp.one_lt⟩
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) p
    have ht : (rootsOfUnity.mkOfPowEq ζ hζ.pow_eq_one : (AlgebraicClosure ℚ)ˣ) ∈ rootsOfUnity p (AlgebraicClosure ℚ) :=
      (rootsOfUnity.mkOfPowEq ζ hζ.pow_eq_one).2
    have hspec := modularCyclotomicCharacter.spec (AlgebraicClosure ℚ) (card_rootsOfUnity_eq_self p)
      (complexConjugation : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) ht
    have hval : ((cycloChar p complexConjugation : ZMod p)).val = 1 := by
      rw [hχ, Units.val_one, ZMod.val_one]
    have hχ' : (modularCyclotomicCharacter (AlgebraicClosure ℚ) (card_rootsOfUnity_eq_self p)
        (complexConjugation : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) : ZMod p).val = 1 := hval
    rw [hχ', pow_one, rootsOfUnity.coe_mkOfPowEq] at hspec
    exact cc_apply_ne_of_isPrimitiveRoot hp2 hζ hspec

include h4 hFζ in

theorem arch_free : ∀ (γ : Γ) (h : ↥archimedeanDecomposition),
    γ * archimedeanLoc h * γ⁻¹ ∈ F.fixingSubgroup → h = 1 := by
  intro γ h hmem
  rcases coe_eq_one_or_eq_cc h with h1 | hc
  · exact Subtype.ext h1
  · exfalso
    have : archimedeanLoc h = complexConjugation := hc
    rw [this] at hmem
    exact conj_cc_not_mem F h4 hFζ γ hmem

end ArchFree

section CoindFin

variable {k : Type} [Field k] (U : Subgroup Γ) (N : Rep k ↥U)

abbrev C : Rep k Γ := Rep.coind U.subtype N

lemma C_apply_umul (f : C U N) (u : ↥U) (x : Γ) : (f : Γ → N) ((u : Γ) * x) = N.ρ u ((f : Γ → N) x) := f.2 u x

lemma C_ρ_apply (g : Γ) (f : C U N) (x : Γ) : ((C U N).ρ g f : Γ → N) x = (f : Γ → N) (x * g) := rfl

variable [U.FiniteIndex]

attribute [local instance] Fintype.ofFinite

lemma finiteDimensional_C [FiniteDimensional k N] : FiniteDimensional k (C U N) := by
  classical
  let ev : C U N →ₗ[k] (Γ ⧸ U → N) :=
    { toFun := fun f c => (f : Γ → N) (Quotient.out c)⁻¹
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine Module.Finite.of_injective ev fun f f' h => ?_
  apply Subtype.ext
  funext y
  set c : Γ ⧸ U := QuotientGroup.mk y⁻¹
  have hu : y * Quotient.out c ∈ U := by
    have : QuotientGroup.mk (Quotient.out c) = c := Quotient.out_eq c
    rw [QuotientGroup.eq] at this
    simpa using (inv_mem this)
  have hy : y = (y * Quotient.out c) * (Quotient.out c)⁻¹ := by group
  have hf := congrFun h c
  simp only [ev, LinearMap.coe_mk, AddHom.coe_mk] at hf
  have h1 := C_apply_umul U N f ⟨_, hu⟩ (Quotient.out c)⁻¹
  have h2 := C_apply_umul U N f' ⟨_, hu⟩ (Quotient.out c)⁻¹
  rw [hy, h1, h2, hf]

variable (χ : Γ →* kˣ) (hχ : ∀ u ∈ U, χ u = 1) (hN : ∀ u : ↥U, N.ρ u = 1)

def frTerm (φ : Module.Dual k N) (f : C U N) : Γ ⧸ U → k :=
  Quotient.lift (fun γ : Γ => (χ γ : k) * φ ((f : Γ → N) γ⁻¹)) (by
    intro a b hab'
    have hab : a⁻¹ * b ∈ U := QuotientGroup.leftRel_apply.mp hab'
    have hb : b = a * (a⁻¹ * b) := by group
    change (χ a : k) * φ ((f : Γ → N) a⁻¹) = (χ b : k) * φ ((f : Γ → N) b⁻¹)
    conv_rhs => rw [hb]
    rw [map_mul, hχ _ hab, mul_one, mul_inv_rev]
    have := C_apply_umul U N f ⟨(a⁻¹ * b)⁻¹, inv_mem hab⟩ a⁻¹
    simp only at this
    rw [this, hN, Module.End.one_apply])

omit [U.FiniteIndex] in
lemma frTerm_mk (φ : Module.Dual k N) (f : C U N) (γ : Γ) :
    frTerm U N χ hχ hN φ f (QuotientGroup.mk γ) = (χ γ : k) * φ ((f : Γ → N) γ⁻¹) := rfl

def frFun (φ : Module.Dual k N) : Module.Dual k (C U N) where
  toFun f := ∑ c : Γ ⧸ U, frTerm U N χ hχ hN φ f c
  map_add' f f' := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    induction c using QuotientGroup.induction_on with
    | H g => simp [frTerm_mk, mul_add]
  map_smul' r f := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    induction c using QuotientGroup.induction_on with
    | H g => simp [frTerm_mk, mul_left_comm]

lemma frFun_apply (φ : Module.Dual k N) (f : C U N) :
    frFun U N χ hχ hN φ f = ∑ c : Γ ⧸ U, frTerm U N χ hχ hN φ f c := rfl

lemma frFun_ρ (φ : Module.Dual k N) (g : Γ) (f : C U N) :
    frFun U N χ hχ hN φ ((C U N).ρ g f) = (χ g : k) * frFun U N χ hχ hN φ f := by
  classical
  rw [frFun_apply, frFun_apply, Finset.mul_sum]

  refine Fintype.sum_equiv (MulAction.toPerm (g⁻¹ : Γ) : Equiv.Perm (Γ ⧸ U)) _ _ fun c => ?_
  induction c using QuotientGroup.induction_on with
  | H x =>
    change frTerm U N χ hχ hN φ ((C U N).ρ g f) (QuotientGroup.mk x) =
      (χ g : k) * frTerm U N χ hχ hN φ f (QuotientGroup.mk (g⁻¹ * x))
    rw [frTerm_mk, frTerm_mk, C_ρ_apply, mul_inv_rev, inv_inv, map_mul, map_inv, Units.val_mul, ← mul_assoc,
      Units.mul_inv_cancel_left]

lemma frFun_mem_invariants (φ : Module.Dual k N) :
    frFun U N χ hχ hN φ ∈ ((C U N).dualTwist χ).ρ.invariants := by
  intro g
  rw [Rep.dualTwist_ρ_apply]
  apply LinearMap.ext
  intro f
  rw [LinearMap.smul_apply, LinearMap.comp_apply, frFun_ρ, smul_eq_mul, ← mul_assoc, map_inv, Units.val_inv_eq_inv_val,
    mul_inv_cancel₀ (χ g).ne_zero, one_mul]

def frLin : Module.Dual k N →ₗ[k] ((C U N).dualTwist χ).ρ.invariants where
  toFun φ := ⟨frFun U N χ hχ hN φ, frFun_mem_invariants U N χ hχ hN φ⟩
  map_add' φ ψ := by
    apply Subtype.ext; apply LinearMap.ext; intro f
    change ∑ c, frTerm U N χ hχ hN (φ + ψ) f c = ∑ c, frTerm U N χ hχ hN φ f c + ∑ c, frTerm U N χ hχ hN ψ f c
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    induction c using QuotientGroup.induction_on with
    | H g => simp [frTerm_mk, mul_add]
  map_smul' r φ := by
    apply Subtype.ext; apply LinearMap.ext; intro f
    change ∑ c, frTerm U N χ hχ hN (r • φ) f c = r • ∑ c, frTerm U N χ hχ hN φ f c
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    induction c using QuotientGroup.induction_on with
    | H g => simp [frTerm_mk, mul_left_comm]

def deltaC (n : N) : C U N :=
  ⟨fun x => by classical exact if x ∈ U then n else 0, by
    classical
    intro u x
    change (if (u : Γ) * x ∈ U then n else 0) = N.ρ u (if x ∈ U then n else 0)
    by_cases hx : x ∈ U
    · rw [if_pos hx, if_pos (mul_mem u.2 hx), hN u, Module.End.one_apply]
    · rw [if_neg hx, if_neg (fun h => hx (by simpa using mul_mem (inv_mem u.2) h)), map_zero]⟩

omit [U.FiniteIndex] in
lemma deltaC_apply (n : N) (x : Γ) : (deltaC U N hN n : Γ → N) x = by classical exact if x ∈ U then n else 0 := rfl

lemma frFun_deltaC (φ : Module.Dual k N) (n : N) : frFun U N χ hχ hN φ (deltaC U N hN n) = φ n := by
  classical
  rw [frFun_apply, Finset.sum_eq_single (QuotientGroup.mk 1 : Γ ⧸ U)]
  · rw [frTerm_mk, inv_one, deltaC_apply, if_pos (one_mem U), map_one, Units.val_one, one_mul]
  · intro c _ hc
    induction c using QuotientGroup.induction_on with
    | H x =>
      rw [frTerm_mk, deltaC_apply, if_neg, map_zero, mul_zero]
      intro hx
      apply hc
      rw [QuotientGroup.eq]
      simpa using hx
  · intro h; exact absurd (Finset.mem_univ _) h

lemma frLin_injective : Function.Injective (frLin U N χ hχ hN) := by
  intro φ ψ h
  apply LinearMap.ext
  intro n
  have := congrArg (fun F : ((C U N).dualTwist χ).ρ.invariants => (F : Module.Dual k (C U N)) (deltaC U N hN n)) h
  change frFun U N χ hχ hN φ (deltaC U N hN n) = frFun U N χ hχ hN ψ (deltaC U N hN n) at this
  rwa [frFun_deltaC, frFun_deltaC] at this

include hχ hN in

theorem finrank_le_finrank_invariants_dualTwist [FiniteDimensional k N] :
    Module.finrank k N ≤ Module.finrank k ((C U N).dualTwist χ).ρ.invariants := by
  haveI : FiniteDimensional k (C U N) := finiteDimensional_C U N
  haveI : FiniteDimensional k ((C U N).dualTwist χ) := by
    change FiniteDimensional k (Module.Dual k (C U N)); infer_instance
  rw [← Subspace.dual_finrank_eq]
  exact LinearMap.finrank_le_finrank_of_injective (frLin_injective U N χ hχ hN)

end CoindFin

section Push

variable (S : Finset Nat.Primes) {k : Type} [CommRing k]
  {A B : Rep k (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)}
  (ψ : A →ₗ[k] B) (hψ : ∀ (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (a : A), ψ (A.ρ g a) = B.ρ g (ψ a))

lemma cochainsPullPush₂_id_eq
    (x : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → A) :
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

def continuousH2SMap : continuousH2S S A →ₗ[k] continuousH2S S B :=
  Submodule.mapQ _ _ (levelCocyclesS₂Map S ψ hψ) fun _ hx => pushS_mem_levelCoboundariesS₂ S ψ hψ hx

abbrev locPush {H : Type} [Group H] (f : H →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) :
    continuousH2 f (Rep.res f A) →ₗ[k] continuousH2 f (Rep.res f B) :=
  continuousH2Map (rH := f) (rG := f) (MonoidHom.id H) (fun _ => rfl)
    (ψ : Rep.res f A →ₗ[k] Rep.res f B) (fun g a => hψ (f g) a)

lemma locRes₂S_continuousH2SMap {H : Type} [Group H] (f : H →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (x : continuousH2S S A) :
    locRes₂S S B f (continuousH2SMap S ψ hψ x) = locPush ψ hψ f (locRes₂S S A f x) := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

lemma locPush_locPush {C : Rep k (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)}
    (ψ' : B →ₗ[k] C) (hψ' : ∀ (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (b : B), ψ' (B.ρ g b) = C.ρ g (ψ' b))
    {H : Type} [Group H] (f : H →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (y : continuousH2 f (Rep.res f A)) :
    locPush ψ' hψ' f (locPush ψ hψ f y) =
      locPush (ψ' ∘ₗ ψ) (fun g a => by rw [LinearMap.comp_apply, hψ, hψ']; rfl) f y := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rfl

lemma locPush_sub_smul {H : Type} [Group H] (f : H →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (y w : continuousH2 f (Rep.res f A)) (c : k) :
    locPush ψ hψ f (y - c • w) = locPush ψ hψ f y - c • locPush ψ hψ f w := by
  rw [map_sub, map_smul]

end Push

section CoindMaps

variable {k : Type} [CommRing k] (U : Subgroup Γ) {N N' : Rep k ↥U}
  (ψ : N →ₗ[k] N') (hψ : ∀ (u : ↥U) (n : N), ψ (N.ρ u n) = N'.ρ u (ψ n))

def coindLin : Rep.coind U.subtype N →ₗ[k] Rep.coind U.subtype N' where
  toFun f := ⟨ψ ∘ (f : Γ → N), fun u x => by
    simp only [Function.comp_apply]
    rw [f.2 u x, hψ]⟩
  map_add' f f' := by apply Subtype.ext; funext x; simp
  map_smul' r f := by apply Subtype.ext; funext x; simp

@[scoped simp] lemma coindLin_apply (f : Rep.coind U.subtype N) (x : Γ) :
    (coindLin U ψ hψ f : Γ → N') x = ψ ((f : Γ → N) x) := rfl

lemma coindLin_equivariant (g : Γ) (f : Rep.coind U.subtype N) :
    coindLin U ψ hψ ((Rep.coind U.subtype N).ρ g f) = (Rep.coind U.subtype N').ρ g (coindLin U ψ hψ f) := by
  apply Subtype.ext; funext x; rfl

end CoindMaps

section Assembly

variable {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (U : Subgroup Γ)
  (N : Rep (ZMod p) ↥U) (hN : ∀ u : ↥U, N.ρ u = 1)

variable (p) in

abbrev T : Rep (ZMod p) ↥U := Rep.trivial (ZMod p) ↥U (ZMod p)

abbrev πL (φ : Module.Dual (ZMod p) N) : Rep.coind U.subtype N →ₗ[ZMod p] Rep.coind U.subtype (T p U) :=
  coindLin U (N' := T p U) φ (fun u n => by rw [hN u]; rfl)

abbrev ιL (v : N) : Rep.coind U.subtype (T p U) →ₗ[ZMod p] Rep.coind U.subtype N :=
  coindLin U (N := T p U) (LinearMap.toSpanSingleton (ZMod p) N v) (fun u c => by
    rw [hN u]; rfl)

lemma πL_equivariant (φ : Module.Dual (ZMod p) N) (g : Γ) (f : Rep.coind U.subtype N) :
    πL U N hN φ ((Rep.coind U.subtype N).ρ g f) = (Rep.coind U.subtype (T p U)).ρ g (πL U N hN φ f) :=
  coindLin_equivariant U _ _ g f

lemma ιL_equivariant (v : N) (g : Γ) (f : Rep.coind U.subtype (T p U)) :
    ιL U N hN v ((Rep.coind U.subtype (T p U)).ρ g f) = (Rep.coind U.subtype N).ρ g (ιL U N hN v f) :=
  coindLin_equivariant U _ _ g f

lemma sum_ιL_πL {ι : Type} [Fintype ι] (b : Basis ι (ZMod p) N) (f : Rep.coind U.subtype N) :
    ∑ i, ιL U N hN (b i) (πL U N hN (b.coord i) f) = f := by
  apply Subtype.ext
  funext x
  rw [Submodule.coe_sum, Finset.sum_apply]
  exact b.sum_repr ((f : Γ → N) x)

variable {H : Type} [Group H] (r : H →* Γ)

lemma sum_locPush_ιL_πL {ι : Type} [Fintype ι] (b : Basis ι (ZMod p) N)
    (y : continuousH2 r (Rep.res r (Rep.coind U.subtype N))) :
    ∑ i, locPush (ιL U N hN (b i)) (ιL_equivariant U N hN (b i)) r
        (locPush (πL U N hN (b.coord i)) (πL_equivariant U N hN (b.coord i)) r y) = y := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  simp only [locPush_locPush]
  change ∑ i, continuousH2π r _ (levelCocycles₂Map (MonoidHom.id H) (fun _ => rfl) _ _ c) = continuousH2π r _ c
  rw [← map_sum]
  congr 1
  apply Subtype.ext
  rw [Submodule.coe_sum]
  funext st
  rw [Finset.sum_apply]
  simp only [coe_levelCocycles₂Map, cochainsPullPush₂_apply, MonoidHom.id_apply, LinearMap.comp_apply]
  exact sum_ιL_πL U N hN b _

end Assembly

end P2Mb58
p2m_reactivate "P2MW.S_groupCohomology_exists_forall_locRes_continuousH2S_coind_eq_add_sum_of_exists_sq_eq_neg_one.P2Mb58"

end
p2m_reactivate "P2MW.S_groupCohomology_exists_forall_locRes_continuousH2S_coind_eq_add_sum_of_exists_sq_eq_neg_one.P2Mb58"

open P2Mb58 in
theorem solution
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [IsGalois ℚ F] (hF : F.IsUnramifiedOutside S)
    (h4 : p = 2 → ∃ i ∈ F, i ^ 2 = -1)
    (hFζ : ∀ s ∈ F.fixingSubgroup, cycloChar p s = 1)
    (N : Rep (ZMod p) ↥F.fixingSubgroup) [FiniteDimensional (ZMod p) N] (hN : ∀ u : ↥F.fixingSubgroup, N.ρ u = 1) :
    ∃ (n : ℕ) (w : Fin n → ∀ q : ↥S, continuousH2 (extArithLoc S (Sum.inr q))
        (Rep.res (extArithLoc S (Sum.inr q)) (Rep.coind F.fixingSubgroup.subtype N))),
      n ≤ Module.finrank (ZMod p) ((Rep.coind F.fixingSubgroup.subtype N).dualTwist (cycloChar p)).ρ.invariants ∧
      ∀ z : ∀ q : ↥S, continuousH2 (extArithLoc S (Sum.inr q))
          (Rep.res (extArithLoc S (Sum.inr q)) (Rep.coind F.fixingSubgroup.subtype N)),
        ∃ (x : continuousH2S S (Rep.coind F.fixingSubgroup.subtype N)) (c : Fin n → ZMod p),
          locRes₂S S (Rep.coind F.fixingSubgroup.subtype N) (extArithLoc S (Sum.inl ())) x = 0 ∧
          ∀ q : ↥S, z q = locRes₂S S (Rep.coind F.fixingSubgroup.subtype N) (extArithLoc S (Sum.inr q)) x
            + ∑ i, c i • w i q := by
  classical
  haveI : FiniteDimensional ℚ F := hF.1
  haveI hUfin : F.fixingSubgroup.FiniteIndex := by
    have := groupCohomology.finiteIndex_comap_fixingSubgroup
      (MonoidHom.id (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) F
    rwa [Subgroup.comap_id] at this

  obtain ⟨w, hw⟩ :=
    groupCohomology.exists_forall_locRes_continuousH2S_coind_trivial_eq_add_smul S hpS F hF h4 hFζ
  let b : Basis (Fin (Module.finrank (ZMod p) N)) (ZMod p) N := Module.finBasis (ZMod p) N
  refine ⟨Module.finrank (ZMod p) N,
    fun i q => locPush (ιL F.fixingSubgroup N hN (b i)) (ιL_equivariant F.fixingSubgroup N hN (b i))
      (extArithLoc S (Sum.inr q)) (w q), ?_, ?_⟩
  ·
    exact finrank_le_finrank_invariants_dualTwist F.fixingSubgroup N (cycloChar p) hFζ hN
  · intro z
    choose x c hxc using fun i : Fin (Module.finrank (ZMod p) N) =>
      hw (fun q => locPush (πL F.fixingSubgroup N hN (b.coord i)) (πL_equivariant F.fixingSubgroup N hN (b.coord i))
        (extArithLoc S (Sum.inr q)) (z q))
    refine ⟨∑ i, continuousH2SMap S (ιL F.fixingSubgroup N hN (b i)) (ιL_equivariant F.fixingSubgroup N hN (b i)) (x i),
      c, ?_, ?_⟩
    ·
      haveI : FiniteDimensional (ZMod p) (Rep.coind F.fixingSubgroup.subtype N) := finiteDimensional_C F.fixingSubgroup N
      have hH1 : Subsingleton (H1 (Rep.res (extArithLoc S (Sum.inl ())) (Rep.coind F.fixingSubgroup.subtype N))) :=
        subsingleton_H1_of_free (extArithLoc S (Sum.inl ())) F.fixingSubgroup N (arch_free F h4 hFζ)
      haveI := TWNum.subsingleton_continuousH2_extArithLoc_inl S (Rep.coind F.fixingSubgroup.subtype N) hH1
      exact Subsingleton.elim _ _
    · intro q
      have hres : ∀ i, locRes₂S S (Rep.coind F.fixingSubgroup.subtype (T p F.fixingSubgroup)) (extArithLoc S (Sum.inr q)) (x i)
          = locPush (πL F.fixingSubgroup N hN (b.coord i)) (πL_equivariant F.fixingSubgroup N hN (b.coord i))
              (extArithLoc S (Sum.inr q)) (z q) - c i • w q := fun i => by
        rw [hxc i q, add_sub_cancel_right]
      rw [map_sum]
      simp only [locRes₂S_continuousH2SMap, hres, map_sub, map_smul]
      have key := sum_locPush_ιL_πL F.fixingSubgroup N hN (extArithLoc S (Sum.inr q)) b (z q)
      rw [Finset.sum_sub_distrib, key, sub_add_cancel]

end S_groupCohomology_exists_forall_locRes_continuousH2S_coind_eq_add_sum_of_exists_sq_eq_neg_one
end P2MW
export P2MW.S_groupCohomology_exists_forall_locRes_continuousH2S_coind_eq_add_sum_of_exists_sq_eq_neg_one (solution)
