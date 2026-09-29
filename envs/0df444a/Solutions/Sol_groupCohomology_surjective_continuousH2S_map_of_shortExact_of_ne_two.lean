-- Prove2me | solution 1 for groupCohomology.surjective_continuousH2S_map_of_shortExact_of_ne_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/74e86018-d36b-55ff-82dd-aeda43266a61

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Theorems.Thm_groupCohomology_exists_isUnramifiedOutside_forall_apply_eq_one_of_smooth
import Theorems.Thm_IntermediateField_exists_normal_isUnramifiedOutside_of_le
import Theorems.Thm_groupCohomology_exists_isLevelConstant_inhomogeneousCochains_d_eq_of_ne_two
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_surjective_continuousH2S_map_of_shortExact_of_ne_two
p2m_attr_erase "instance" "NumberField.LevelArith.instCommGroupUnitsModPow M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete groupCohomology.normal_comap_fixingSubgroup groupCohomology.finiteIndex_comap_fixingSubgroup AlgebraicClosure.Rat.isGalois FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap NumberField.AdelicHaar.locallyCompactSpace_adeleRing NumberField.AdelicHaar.finite_residueField_adicCompletionIntegers NumberField.AdelicHaar.locallyCompactSpace_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_finiteAdeleRing NumberField.AdelicHaar.compactSpace_adicCompletionIntegers NumberField.AdelicHaar.t2Space_finiteAdeleRing NumberField.AdelicHaar.t2Space_matrix_adeleRing NumberField.AdelicHaar.t2Space_adeleRing NumberField.AdelicHaar.fact_isOpen_adicCompletionIntegers NumberField.AdelicHaar.t2Space_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_matrix_adeleRing NumberField.AdelicHaar.t2Space_infiniteAdeleRing NumberField.AdelicHaar.properSpace_adicCompletion ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex"
p2m_attr_erase "instance" "ExtCitation.inertiaPullback_normal M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite Deep.NTSupply.instNormalRayClassSubgroup instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal"
p2m_attr_erase "simp" "groupCohomology.coe_continuousH1SrMap_apply groupCohomology.continuousH2SrMap_continuousH2Srπ groupCohomology.coe_levelCocyclesSr₂Map NumberField.LevelArith.coe_levelFieldEquiv NumberField.LevelArith.modP_apply_mk NumberField.LevelArith.coe_levelFieldEquiv_symm NumberField.LevelArith.torsionP_apply_coe NumberField.LevelArith.repTorsionPMap_hom_apply_coe NumberField.LevelArith.toZMod_apply NumberField.LevelArith.repModPMap_hom_mk NumberField.SUnits.val_zsmul NumberField.SUnits.val_add NumberField.LevelArith.smul_mk NumberField.LevelArith.selmerRepInt_ρ_apply NumberField.LevelArith.selmerRepField_ρ_apply NumberField.LevelArith.unitsModPowMap_mk M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk M4aHerbrand.IdeleGaloisDescent.classAct_mk M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq ExtCitation.LocalLevel.coe_smul_OO WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply groupCohomology.continuousH2Inflation_H2π groupCohomology.levelInflate₂_apply groupCohomology.coe_levelInflateCocycles₂ groupCohomology.levelInflate₁_apply M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply"
p2m_attr_erase "simp" "FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul"
p2m_attr_erase "simp" "TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply"
p2m_attr_erase "simp" "LinearEquiv.restrictedProductCongrLeft'_apply GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl IsLocalRing.principalUnits_zero groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply M4aHerbrand.Bridge.finiteConorm_apply M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent AutomorphicForm.CuspidalityNotion.mk.injEq"
p2m_attr_erase "simp" "AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec Rep.coe_tateδneg2_apply Representation.TateResCor.cosetDecomp_apply Rep.coe_tateHneg1Res_apply Representation.TateResCor.coe_tateHneg1Cores_apply Representation.TateResCor.tateH0Res_mk Rep.coe_tateHneg1Cores_apply Rep.tateH0Res_mk Representation.TateResCor.coe_cosetNormInvariants_apply Rep.tateH0Cores_mk Representation.TateResCor.coinvariantsCores_mk Representation.TateResCor.coinvariantsTransfer_mk Representation.TateResCor.tateH0Cores_mk Representation.TateResCor.coe_tateHneg1Res_apply"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000
open CategoryTheory Module groupCohomology ExtCitation

namespace P2mS25RX

local notation "Γ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

variable {S : Finset Nat.Primes} {k : Type} [CommRing k] {A B : Rep.{0} k Γ} (φ : A ⟶ B)

lemma d₂₃_comp (e : Γ × Γ → A) : (d₂₃ B).hom (φ.hom ∘ e) = φ.hom ∘ (d₂₃ A).hom e := by
  funext ⟨g, h, j⟩
  simp only [d₂₃_hom_apply, Function.comp_apply, map_add, map_sub, Rep.hom_comm_apply]

lemma lcS₂_sub {X : Type*} [AddGroup X] {f f' : Γ × Γ → X} (hf : IsLevelConstantS₂ S f) (hf' : IsLevelConstantS₂ S f') :
    IsLevelConstantS₂ S (f - f') := by
  obtain ⟨F, hF, h⟩ := hf
  obtain ⟨F', hF', h'⟩ := hf'
  refine ⟨F ⊔ F', hF.sup hF', fun g g' s s' hs hs' => ?_⟩
  simp only [Pi.sub_apply]
  rw [h g g' s s' (IntermediateField.fixingSubgroup_antitone le_sup_left hs)
      (IntermediateField.fixingSubgroup_antitone le_sup_left hs'),
    h' g g' s s' (IntermediateField.fixingSubgroup_antitone le_sup_right hs)
      (IntermediateField.fixingSubgroup_antitone le_sup_right hs')]

lemma conj_mem_fixingSubgroup (E : IntermediateField ℚ (AlgebraicClosure ℚ)) [hE : Normal ℚ E]
    {s : Γ} (hs : s ∈ E.fixingSubgroup) (h : Γ) : h⁻¹ * s * h ∈ E.fixingSubgroup := by
  letI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  letI : IsAlgClosure ℚ (AlgebraicClosure ℚ) := ⟨inferInstance, inferInstance⟩
  letI : Normal ℚ (AlgebraicClosure ℚ) := IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)
  rw [IntermediateField.mem_fixingSubgroup_iff] at hs ⊢
  intro x hx
  have hhx : h x ∈ E := (IntermediateField.normal_iff_forall_map_le'.1 hE h) ⟨x, hx, rfl⟩
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hs _ hhx]
  simp

lemma exists_normal_level₂ {X : Type*} {b : Γ × Γ → X} (hb : IsLevelConstantS₂ S b) :
    ∃ E : IntermediateField ℚ (AlgebraicClosure ℚ), E.IsUnramifiedOutside S ∧ Normal ℚ E ∧
      ∀ g g' s s', s ∈ E.fixingSubgroup → s' ∈ E.fixingSubgroup → b (g * s, g' * s') = b (g, g') := by
  obtain ⟨F, hF, h⟩ := hb
  obtain ⟨E, hFE, hE, hEn⟩ := IntermediateField.exists_normal_isUnramifiedOutside_of_le S F hF
  exact ⟨E, hE, hEn, fun g g' s s' hs hs' => h g g' s s' (IntermediateField.fixingSubgroup_antitone hFE hs)
    (IntermediateField.fixingSubgroup_antitone hFE hs')⟩

lemma lc₃_d₂₃ {L : IntermediateField ℚ (AlgebraicClosure ℚ)} (hLS : L.IsUnramifiedOutside S)
    (hL : ∀ s ∈ L.fixingSubgroup, A.ρ s = 1) {b : Γ × Γ → A} (hb : IsLevelConstantS₂ S b) :
    ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧
      ∀ g₁ g₂ g₃ s₁ s₂ s₃ : Γ, s₁ ∈ F.fixingSubgroup → s₂ ∈ F.fixingSubgroup → s₃ ∈ F.fixingSubgroup →
        (d₂₃ A).hom b (g₁ * s₁, g₂ * s₂, g₃ * s₃) = (d₂₃ A).hom b (g₁, g₂, g₃) := by
  obtain ⟨E, hE, hEn, h⟩ := exists_normal_level₂ hb
  haveI := hEn
  refine ⟨E ⊔ L, hE.sup hLS, fun g₁ g₂ g₃ s₁ s₂ s₃ hs₁ hs₂ hs₃ => ?_⟩
  have h1E : s₁ ∈ E.fixingSubgroup := IntermediateField.fixingSubgroup_antitone le_sup_left hs₁
  have h2E : s₂ ∈ E.fixingSubgroup := IntermediateField.fixingSubgroup_antitone le_sup_left hs₂
  have h3E : s₃ ∈ E.fixingSubgroup := IntermediateField.fixingSubgroup_antitone le_sup_left hs₃
  have h1L : s₁ ∈ L.fixingSubgroup := IntermediateField.fixingSubgroup_antitone le_sup_right hs₁
  simp only [d₂₃_hom_apply]
  have e1 : g₁ * s₁ * (g₂ * s₂) = g₁ * g₂ * (g₂⁻¹ * s₁ * g₂ * s₂) := by group
  have e2 : g₂ * s₂ * (g₃ * s₃) = g₂ * g₃ * (g₃⁻¹ * s₂ * g₃ * s₃) := by group
  have m1 : g₂⁻¹ * s₁ * g₂ * s₂ ∈ E.fixingSubgroup := E.fixingSubgroup.mul_mem (conj_mem_fixingSubgroup E h1E g₂) h2E
  have m2 : g₃⁻¹ * s₂ * g₃ * s₃ ∈ E.fixingSubgroup := E.fixingSubgroup.mul_mem (conj_mem_fixingSubgroup E h2E g₃) h3E
  rw [e1, e2, h (g₁ * g₂) g₃ _ _ m1 h3E, h g₁ (g₂ * g₃) _ _ h1E m2, h g₂ g₃ _ _ h2E h3E, h g₁ g₂ _ _ h1E h2E,
    map_mul, Module.End.mul_apply, hL s₁ h1L, Module.End.one_apply]

lemma comp_injective (hφ : Function.Injective φ.hom) {ι : Type*} {x y : ι → A}
    (h : φ.hom ∘ x = φ.hom ∘ y) : x = y :=
  funext fun i => hφ (congrFun h i)

end P2mS25RX

open P2mS25RX in

theorem solution
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (N1 N2 N3 : Rep.{0} (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    [FiniteDimensional (ZMod p) N1] [FiniteDimensional (ZMod p) N2] [FiniteDimensional (ZMod p) N3]
    (f : N1 ⟶ N2) (g : N2 ⟶ N3) (hfg : f ≫ g = 0)
    (hex : (ShortComplex.mk f g hfg).ShortExact)
    (hsm : ∀ m : N2, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s ∈ F.fixingSubgroup, N2.ρ s m = m)
    (hur : ∀ q : Nat.Primes, q ∉ S → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
      A.LiesOverPrime (q : ℕ) → ∀ s ∈ A.inertiaSubgroupIn ℚ, N2.ρ s = 1)
    (p₂ : continuousH2S S N2 →ₗ[ZMod p] continuousH2S S N3)
    (hp₂ : ∀ (z : levelCocyclesS₂ S N2) (z' : levelCocyclesS₂ S N3),
        (∀ st, (z' : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → N3) st = g.hom ((z : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → N2) st)) → p₂ (continuousH2Sπ S N2 z) = continuousH2Sπ S N3 z') :
    Function.Surjective p₂ := by

  have hinjf : Function.Injective f.hom := (Rep.mono_iff_injective f).1 hex.mono_f
  have hsurg : Function.Surjective g.hom := (Rep.epi_iff_surjective g).1 hex.epi_g
  have hM := hex.map_of_exact (forget₂ (Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (ModuleCat (ZMod p)))
  have hrk : LinearMap.range f.hom.toLinearMap = LinearMap.ker g.hom.toLinearMap := hM.exact.moduleCat_range_eq_ker

  obtain ⟨σ, hσ⟩ := g.hom.toLinearMap.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hsurg)
  obtain ⟨π, hπ⟩ := f.hom.toLinearMap.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 hinjf)
  have hσ' : ∀ x, g.hom (σ x) = x := fun x => LinearMap.congr_fun hσ x
  have hπ' : ∀ a, π (f.hom a) = a := fun a => LinearMap.congr_fun hπ a
  have hfπ : ∀ b : N2, g.hom b = 0 → f.hom (π b) = b := fun b hb => by
    obtain ⟨a, rfl⟩ : b ∈ LinearMap.range f.hom.toLinearMap := by rw [hrk]; exact hb
    exact congrArg f.hom (hπ' a)

  have hsm1 : ∀ m : N1, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s ∈ F.fixingSubgroup, N1.ρ s m = m := fun m => by
    obtain ⟨F, hF, h⟩ := hsm (f.hom m)
    exact ⟨F, hF, fun s hs => hinjf (by rw [Rep.hom_comm_apply, h s hs])⟩
  have hur1 : ∀ q : Nat.Primes, q ∉ S → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
      A.LiesOverPrime (q : ℕ) → ∀ s ∈ A.inertiaSubgroupIn ℚ, N1.ρ s = 1 := fun q hq A hA s hs => by
    apply LinearMap.ext; intro m
    apply hinjf
    rw [Rep.hom_comm_apply, hur q hq A hA s hs]
    rfl

  intro y
  obtain ⟨z₃, rfl⟩ := Submodule.mkQ_surjective _ y
  obtain ⟨hz₃c, F, hF, hz₃l⟩ := (mem_levelCocyclesS₂_iff S N3 _).1 z₃.2

  obtain ⟨L, hLS, hL2⟩ := groupCohomology.exists_isUnramifiedOutside_forall_apply_eq_one_of_smooth S N2 hsm hur
  have hL1 : ∀ s ∈ L.fixingSubgroup, N1.ρ s = 1 := fun s hs => by
    apply LinearMap.ext; intro m; apply hinjf
    rw [Rep.hom_comm_apply, hL2 s hs]; rfl

  set b : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → N2 := σ ∘ (z₃ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → N3) with hb
  have hgb : g.hom ∘ b = (z₃ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → N3) := funext fun st => hσ' _
  have hblc : IsLevelConstantS₂ S b := ⟨F, hF, fun g₁ g₂ s₁ s₂ hs₁ hs₂ => by
    simp only [hb, Function.comp_apply, hz₃l g₁ g₂ s₁ s₂ hs₁ hs₂]⟩

  set c := (d₂₃ N2).hom b with hc
  have hgc : g.hom ∘ c = 0 := by
    rw [hc, ← d₂₃_comp, hgb, LinearMap.mem_ker.1 hz₃c]
  set u : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → N1 := π ∘ c with hu
  have hfu : f.hom ∘ u = c := funext fun st => hfπ _ (congrFun hgc st)

  obtain ⟨F₃, hF₃, hclc⟩ := lc₃_d₂₃ hLS hL2 hblc
  have hulc : ∀ g₁ g₂ g₃ s₁ s₂ s₃ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), s₁ ∈ F₃.fixingSubgroup → s₂ ∈ F₃.fixingSubgroup → s₃ ∈ F₃.fixingSubgroup →
      u (g₁ * s₁, g₂ * s₂, g₃ * s₃) = u (g₁, g₂, g₃) := fun g₁ g₂ g₃ s₁ s₂ s₃ h₁ h₂ h₃ => by
    simp only [hu, Function.comp_apply]
    rw [hc, hclc g₁ g₂ g₃ s₁ s₂ s₃ h₁ h₂ h₃]

  let b' : (Fin 2 → (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) → N2 := (cochainsIso₂ N2).inv b
  let u' : (Fin 3 → (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) → N1 := (cochainsIso₃ N1).inv u
  have hu' : ∀ x : Fin 3 → (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), u' x = u (x 0, x 1, x 2) := fun x => rfl
  have hfu' : ((cochainsMap (MonoidHom.id (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) f).f 3).hom u' = ((inhomogeneousCochains N2).d 2 3).hom b' := by
    rw [groupCohomology.eq_d₂₃_comp_inv_apply, ← hc, ← hfu]
    rfl
  have hucoc : ((inhomogeneousCochains N1).d 3 4).hom u' = 0 := by

    have h1 := congrArg (fun φ => φ.hom u') ((cochainsMap (MonoidHom.id (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) f).comm 3 4)
    simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at h1
    rw [hfu'] at h1
    have h2 : ((inhomogeneousCochains N2).d 3 4).hom (((inhomogeneousCochains N2).d 2 3).hom b') = 0 := by
      have := congrArg (fun φ => φ.hom b') ((inhomogeneousCochains N2).d_comp_d 2 3 4)
      simpa using this
    rw [h2] at h1

    apply comp_injective f hinjf
    rw [show ⇑f.hom ∘ ((inhomogeneousCochains N1).d 3 4).hom u' = ((cochainsMap (MonoidHom.id (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) f).f 4).hom
        (((inhomogeneousCochains N1).d 3 4).hom u') from rfl, ← h1]
    exact funext fun _ => (map_zero _).symm
  have hulc' : ∀ (x s : Fin 3 → (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)), (∀ i, s i ∈ F₃.fixingSubgroup) → u' (x * s) = u' x := fun x s hs => by
    rw [hu', hu']
    exact hulc _ _ _ _ _ _ (hs 0) (hs 1) (hs 2)

  obtain ⟨w', ⟨Fw, hFw, hw'lc⟩, hdw'⟩ := groupCohomology.exists_isLevelConstant_inhomogeneousCochains_d_eq_of_ne_two
    hp2 S hpS N1 hsm1 hur1 u' ⟨F₃, hF₃, hulc'⟩ hucoc

  let w : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → N1 := (cochainsIso₂ N1).hom w'
  have hw : ∀ g h : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), w (g, h) = w' ![g, h] := fun g h => rfl
  have hwlc : IsLevelConstantS₂ S w := ⟨Fw, hFw, fun g g' s s' hs hs' => by
    rw [hw, hw]
    have : (![g * s, g' * s'] : Fin 2 → (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) = ![g, g'] * ![s, s'] := by
      ext i; fin_cases i <;> rfl
    rw [this]
    exact hw'lc _ _ (fun i => by fin_cases i <;> assumption)⟩
  have hdw : (d₂₃ N1).hom w = u := by
    have := groupCohomology.comp_d₂₃_eq N1
    have h1 := congrArg (fun φ => φ.hom w') this
    simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at h1
    rw [hdw'] at h1
    rw [show w = ((cochainsIso₂ N1).hom).hom w' from rfl, h1]
    exact CategoryTheory.Iso.inv_hom_id_apply (cochainsIso₃ N1) u

  let z₂ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → N2 := b - f.hom ∘ w
  have hz₂c : z₂ ∈ cocycles₂ N2 := by
    apply LinearMap.mem_ker.2
    show (d₂₃ N2).hom (b - f.hom ∘ w) = 0
    rw [map_sub, d₂₃_comp, hdw, hfu, hc, sub_self]
  have hz₂lc : IsLevelConstantS₂ S z₂ := lcS₂_sub hblc (hwlc.comp f.hom)
  have hgf : ∀ a : N1, g.hom (f.hom a) = 0 := fun a => by
    have := congrArg (fun h : N1 ⟶ N3 => h.hom a) hfg
    simpa using this
  have hgz₂ : ∀ st, (z₃ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → N3) st = g.hom (z₂ st) := fun st => by
    simp only [z₂, Pi.sub_apply, Function.comp_apply, map_sub, hgf, sub_zero]
    exact (hσ' _).symm
  refine ⟨continuousH2Sπ S N2 ⟨z₂, (mem_levelCocyclesS₂_iff S N2 _).2 ⟨hz₂c, hz₂lc⟩⟩, ?_⟩
  rw [hp₂ _ z₃ hgz₂]

end S_groupCohomology_surjective_continuousH2S_map_of_shortExact_of_ne_two
end P2MW
export P2MW.S_groupCohomology_surjective_continuousH2S_map_of_shortExact_of_ne_two (solution)
