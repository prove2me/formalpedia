-- Prove2me | solution 1 for groupCohomology.exists_isLevelConstant_d_two_three_eq_trivial_of_cycloChar_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/cdd6a7ed-adb1-57ca-b836-f719e96d87ed

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Theorems.Thm_groupCohomology_exists_natural_localInv_pPrimary_continuousH2Sr_sUnitsMax
import Theorems.Thm_groupCohomology_exists_isLevelConstant_d_two_three_eq_of_pPow_smul_sUnitsMax
import Theorems.Thm_groupCohomology_kummer_degreeThree_exactness_continuousH2Sr_of_smooth_of_divisible
import Theorems.Thm_NumberField_LevelArith_sUnitsMaxRep_smooth_and_divisible
import Theorems.Thm_NumberField_LevelArith_nonempty_repTorsionP_sUnitsMaxRep_iso_trivial_twist_cycloChar
import Theorems.Thm_groupCohomology_exists_nsmul_eq_zero_continuousH2Sr
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_exists_isLevelConstant_d_two_three_eq_trivial_of_cycloChar_eq_one
p2m_attr_erase "instance" "M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete groupCohomology.normal_comap_fixingSubgroup groupCohomology.finiteIndex_comap_fixingSubgroup AlgebraicClosure.Rat.isGalois FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap NumberField.AdelicHaar.locallyCompactSpace_adeleRing NumberField.AdelicHaar.finite_residueField_adicCompletionIntegers NumberField.AdelicHaar.locallyCompactSpace_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_finiteAdeleRing NumberField.AdelicHaar.compactSpace_adicCompletionIntegers NumberField.AdelicHaar.t2Space_finiteAdeleRing NumberField.AdelicHaar.t2Space_matrix_adeleRing NumberField.AdelicHaar.t2Space_adeleRing NumberField.AdelicHaar.fact_isOpen_adicCompletionIntegers NumberField.AdelicHaar.t2Space_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_matrix_adeleRing NumberField.AdelicHaar.t2Space_infiniteAdeleRing NumberField.AdelicHaar.properSpace_adicCompletion ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal"
p2m_attr_erase "instance" "M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite Deep.NTSupply.instNormalRayClassSubgroup instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal"
p2m_attr_erase "simp" "M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk M4aHerbrand.IdeleGaloisDescent.classAct_mk M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq ExtCitation.LocalLevel.coe_smul_OO WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply groupCohomology.continuousH2Inflation_H2π groupCohomology.levelInflate₂_apply groupCohomology.coe_levelInflateCocycles₂ groupCohomology.levelInflate₁_apply M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply"
p2m_attr_erase "simp" "SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff"
p2m_attr_erase "simp" "RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl IsLocalRing.principalUnits_zero groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul"
p2m_attr_erase "simp" "M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply M4aHerbrand.Bridge.finiteConorm_apply M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec Rep.coe_tateδneg2_apply Representation.TateResCor.cosetDecomp_apply Rep.coe_tateHneg1Res_apply Representation.TateResCor.coe_tateHneg1Cores_apply Representation.TateResCor.tateH0Res_mk"
p2m_attr_erase "simp" "Rep.coe_tateHneg1Cores_apply Rep.tateH0Res_mk Representation.TateResCor.coe_cosetNormInvariants_apply Rep.tateH0Cores_mk Representation.TateResCor.coinvariantsCores_mk Representation.TateResCor.coinvariantsTransfer_mk Representation.TateResCor.tateH0Cores_mk Representation.TateResCor.coe_tateHneg1Res_apply"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
open CategoryTheory Module groupCohomology ExtCitation
open NumberField.LevelArith
open scoped NumberField.LevelArith

namespace BrauerDiv

variable (p : ℕ) [hp : Fact p.Prime]

theorem exists_root (x : AddCircle (1 : ℚ)) (hx : ∃ k : ℕ, (p ^ k : ℤ) • x = 0) :
    ∃ y : AddCircle (1 : ℚ), (p : ℤ) • y = x ∧ (∃ k : ℕ, (p ^ k : ℤ) • y = 0) ∧ (x = 0 → y = 0) := by
  by_cases hx0 : x = 0
  · exact ⟨0, by rw [hx0, smul_zero], ⟨0, smul_zero _⟩, fun _ => rfl⟩
  obtain ⟨k, hk⟩ := hx
  induction x using QuotientAddGroup.induction_on with
  | H r =>
    refine ⟨((r / p : ℚ) : AddCircle (1 : ℚ)), ?_, ⟨k + 1, ?_⟩, fun h => absurd h hx0⟩
    · have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
      rw [← AddCircle.coe_zsmul, zsmul_eq_mul, Int.cast_natCast, mul_div_cancel₀ _ hp0]
    · have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
      have h1 : (((p ^ k : ℤ) • r : ℚ) : AddCircle (1 : ℚ)) = 0 := by rw [← hk]; rfl
      rw [← AddCircle.coe_zsmul]
      convert h1 using 2
      rw [zsmul_eq_mul, zsmul_eq_mul]
      push_cast
      rw [pow_succ, mul_assoc, mul_div_cancel₀ _ hp0]

theorem exists_smul_eq {T : Type} [AddCommGroup T] [Module ℤ T] {ι : Type}
    (invQ : T →ₗ[ℤ] (ι → AddCircle (1 : ℚ))) (hinj : Function.Injective invQ)
    (hrange : ∀ f, f ∈ LinearMap.range invQ ↔ (∀ w, ∃ k : ℕ, (p ^ k : ℤ) • f w = 0) ∧ ∑ᶠ w, f w = 0)
    (t : T) : ∃ t' : T, p • t' = t := by
  classical
  obtain ⟨hprim, hsum⟩ := (hrange (invQ t)).mp ⟨t, rfl⟩

  have hroot : ∀ w, ∃ y : AddCircle (1 : ℚ), (p : ℤ) • y = invQ t w ∧ (∃ k : ℕ, (p ^ k : ℤ) • y = 0) ∧ (invQ t w = 0 → y = 0) :=
    fun w => exists_root p (invQ t w) (hprim w)
  choose g₀ hg₀ hg₀prim hg₀zero using hroot
  have hsupp : Function.support g₀ = Function.support (invQ t) := by
    ext w
    simp only [Function.mem_support, ne_eq]
    constructor
    · intro h h0; exact h (hg₀zero w h0)
    · intro h h0; apply h; rw [← hg₀ w, h0, smul_zero]
  by_cases ht0 : invQ t = 0
  · refine ⟨0, hinj ?_⟩
    rw [smul_zero, map_zero, ht0]

  obtain ⟨w₀, hw₀⟩ : ∃ w₀, invQ t w₀ ≠ 0 := Function.ne_iff.mp ht0

  let s : AddCircle (1 : ℚ) := ∑ᶠ w, g₀ w
  have hps : (p : ℤ) • s = 0 := by
    show (p : ℤ) • ∑ᶠ w, g₀ w = 0
    by_cases hfin : (Function.support g₀).Finite
    · have hmap := (zsmulAddGroupHom (p : ℤ) : AddCircle (1 : ℚ) →+ AddCircle (1 : ℚ)).map_finsum hfin
      simp only [zsmulAddGroupHom_apply] at hmap
      rw [hmap]
      simp_rw [hg₀]
      exact hsum
    · rw [finsum_of_infinite_support hfin, smul_zero]
  have hsprim : ∃ k : ℕ, (p ^ k : ℤ) • s = 0 := by
    show ∃ k : ℕ, (p ^ k : ℤ) • ∑ᶠ w, g₀ w = 0
    by_cases hfin : (Function.support g₀).Finite
    ·
      choose kf hkf using hg₀prim
      refine ⟨∑ w ∈ hfin.toFinset, kf w, ?_⟩
      rw [finsum_eq_sum _ hfin, Finset.smul_sum]
      refine Finset.sum_eq_zero fun w hw => ?_
      have hle : kf w ≤ ∑ w ∈ hfin.toFinset, kf w := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hw
      obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hle
      rw [hm, pow_add, mul_comm, mul_smul, hkf w, smul_zero]
    · exact ⟨0, by rw [finsum_of_infinite_support hfin, smul_zero]⟩

  let g : ι → AddCircle (1 : ℚ) := fun w => g₀ w - if w = w₀ then s else 0
  have hg : ∀ w, g w = g₀ w - if w = w₀ then s else 0 := fun _ => rfl
  have hgmem : g ∈ LinearMap.range invQ := by
    rw [hrange]
    constructor
    · intro w
      rw [hg]
      obtain ⟨k₁, hk₁⟩ := hg₀prim w
      obtain ⟨k₂, hk₂⟩ := hsprim
      refine ⟨k₁ + k₂, ?_⟩
      rw [smul_sub, pow_add, mul_comm, mul_smul, mul_smul, hk₁, smul_zero, zero_sub, neg_eq_zero]
      split_ifs
      · rw [smul_comm, hk₂, smul_zero]
      · rw [smul_zero, smul_zero]
    · show ∑ᶠ w, (g₀ w - if w = w₀ then s else 0) = 0
      by_cases hfin : (Function.support g₀).Finite
      · have hfin' : (Function.support fun w => if w = w₀ then s else (0 : AddCircle (1 : ℚ))).Finite :=
          (Set.finite_singleton w₀).subset fun w hw => by
            simp only [Function.mem_support, ne_eq, ite_eq_right_iff, Classical.not_imp] at hw
            exact hw.1
        rw [finsum_sub_distrib hfin hfin', finsum_eq_single _ w₀ fun w hw => if_neg hw, if_pos rfl]
        exact sub_self _
      · have hs0 : s = 0 := finsum_of_infinite_support hfin
        simp only [hs0, ite_self, sub_zero]
        exact finsum_of_infinite_support hfin
  obtain ⟨t', ht'⟩ := hgmem
  refine ⟨t', hinj ?_⟩
  rw [map_nsmul]
  funext w
  rw [Pi.smul_apply, ht', hg, smul_sub, ← natCast_zsmul, hg₀ w]
  split_ifs
  · rw [← natCast_zsmul, hps, sub_zero]
  · rw [smul_zero, sub_zero]

theorem exists_smul_eq_of_torsion {H : Type} [AddCommGroup H]
    (hdiv : ∀ y : H, (∃ k : ℕ, p ^ k • y = 0) → ∃ z : H, p • z = y)
    (y : H) (hy : ∃ n : ℕ, 0 < n ∧ n • y = 0) : ∃ z : H, y = p • z := by
  obtain ⟨n, hn, hny⟩ := hy
  obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' p hp.out.ne_one

  obtain ⟨z₁, hz₁⟩ := hdiv (m • y) ⟨a, by rw [smul_smul]; exact hny⟩

  have hcop : IsCoprime (p : ℤ) (m : ℤ) := Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hm)
  obtain ⟨u, v, huv⟩ := hcop
  refine ⟨u • y + v • z₁, ?_⟩
  calc y = (1 : ℤ) • y := (one_zsmul y).symm
    _ = (u * p + v * m) • y := by rw [huv]
    _ = p • (u • y) + v • (m • y) := by
        rw [add_zsmul, mul_comm u, mul_zsmul, mul_zsmul, natCast_zsmul, natCast_zsmul, smul_comm]
    _ = p • (u • y) + v • (p • z₁) := by rw [hz₁]
    _ = p • (u • y + v • z₁) := by rw [smul_add, smul_comm p v z₁]

end BrauerDiv

noncomputable section

namespace BetaKummer

section transport
variable {k G : Type} [CommRing k] [Group G]

lemma d_comp {n : ℕ} {A B : Rep.{0} k G} (φ : A ⟶ B) (f : (Fin n → G) → A) :
    ((inhomogeneousCochains B).d n (n + 1)).hom (fun g => φ.hom (f g)) = fun g => φ.hom (((inhomogeneousCochains A).d n (n + 1)).hom f g) := by
  rw [inhomogeneousCochains.d_def, inhomogeneousCochains.d_def]
  funext g
  rw [inhomogeneousCochains.d_hom_apply, inhomogeneousCochains.d_hom_apply, map_add, map_sum]
  congr 1
  · exact (Rep.hom_comm_apply φ (g 0) _).symm
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul]

lemma iso_hom_inv_apply {A B : Rep.{0} k G} (φ : A ≅ B) (b : B) : φ.hom.hom (φ.inv.hom b) = b := by
  have h := congrArg (fun f : B ⟶ B => f.hom b) φ.inv_hom_id
  simpa using h

lemma iso_inv_hom_apply {A B : Rep.{0} k G} (φ : A ≅ B) (a : A) : φ.inv.hom (φ.hom.hom a) = a := by
  have h := congrArg (fun f : A ⟶ A => f.hom a) φ.hom_inv_id
  simpa using h

end transport

section twist
variable {p : ℕ} [Fact p.Prime] {G : Type} [Group G] (χ : G →* (ZMod p)ˣ)

lemma d_twist_trivial_eq (hχ : ∀ g, χ g = 1) {n : ℕ} (f : (Fin n → G) → ZMod p) :
    ((inhomogeneousCochains ((Rep.trivial (ZMod p) G (ZMod p)).twist χ)).d n (n + 1)).hom f =
      ((inhomogeneousCochains (Rep.trivial (ZMod p) G (ZMod p))).d n (n + 1)).hom f := by
  rw [inhomogeneousCochains.d_def, inhomogeneousCochains.d_def]
  funext g
  rw [inhomogeneousCochains.d_hom_apply, inhomogeneousCochains.d_hom_apply]
  congr 1
  show ((Rep.trivial (ZMod p) G (ZMod p)).ρ.twist χ) (g 0) _ = _
  rw [Representation.twist_apply_apply, hχ, Units.val_one, one_smul]

end twist

section reading
variable {G : Type} [Group G] (E : Rep.{0} ℤ G) (p : ℕ)

abbrev valF {n : ℕ} (e : (Fin n → G) → repTorsionP p E) : (Fin n → G) → E := fun v => ((e v : repTorsionP p E) : E)

lemma valF_injective {n : ℕ} : Function.Injective (valF E p (n := n)) :=
  fun _ _ h => funext fun v => Subtype.ext (congrFun h v)

lemma valF_d {n : ℕ} (e : (Fin n → G) → repTorsionP p E) :
    valF E p (((inhomogeneousCochains (repTorsionP p E)).d n (n + 1)).hom e) = ((inhomogeneousCochains E).d n (n + 1)).hom (valF E p e) := by
  rw [inhomogeneousCochains.d_def, inhomogeneousCochains.d_def]
  funext g
  show (((inhomogeneousCochains.d (repTorsionP p E) n).hom e g : repTorsionP p E) : E) = (inhomogeneousCochains.d E n).hom (valF E p e) g
  rw [inhomogeneousCochains.d_hom_apply, inhomogeneousCochains.d_hom_apply]
  simp only [Submodule.coe_add, AddSubmonoidClass.coe_finsetSum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  have hcast : ((-1 : ZMod p)) ^ ((j : ℕ) + 1) = (((-1 : ℤ) ^ ((j : ℕ) + 1) : ℤ) : ZMod p) := by push_cast; rfl
  rw [hcast, Int.cast_smul_eq_zsmul, AddSubgroupClass.coe_zsmul]
  exact (int_smul_eq_zsmul _ _ _).symm

end reading

end BetaKummer

end

set_option maxHeartbeats 12800000 in
open BetaKummer in

theorem solution
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (hK : K.IsUnramifiedOutside S) [FiniteDimensional ℚ ↥K]
    (hKζ : ∀ s ∈ K.fixingSubgroup, cycloChar p s = 1)
    (u : (Fin 3 → ↥K.fixingSubgroup) → Rep.trivial (ZMod p) ↥K.fixingSubgroup (ZMod p))
    (hlc : (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧
          ∀ g s : Fin 3 → ↥K.fixingSubgroup,
            (∀ i, ((s i : ↥K.fixingSubgroup) : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) ∈ F.fixingSubgroup) → u (g * s) = u g))
    (hcoc : ((inhomogeneousCochains (Rep.trivial (ZMod p) ↥K.fixingSubgroup (ZMod p))).d 3 4).hom u = 0) :
    ∃ w : (Fin 2 → ↥K.fixingSubgroup) → Rep.trivial (ZMod p) ↥K.fixingSubgroup (ZMod p),
      (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧
          ∀ g s : Fin 2 → ↥K.fixingSubgroup,
            (∀ i, ((s i : ↥K.fixingSubgroup) : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) ∈ F.fixingSubgroup) → w (g * s) = w g) ∧
      ((inhomogeneousCochains (Rep.trivial (ZMod p) ↥K.fixingSubgroup (ZMod p))).d 2 3).hom w = u := by
  classical
  have h4 : p = 2 → ∃ i ∈ K, i ^ 2 = -1 := fun h => absurd h hp2
  have hχ : ∀ g : ↥K.fixingSubgroup, ((cycloChar p).comp K.fixingSubgroup.subtype) g = 1 := fun g => hKζ g g.2

  obtain ⟨φ⟩ := NumberField.LevelArith.nonempty_repTorsionP_sUnitsMaxRep_iso_trivial_twist_cycloChar S hpS K
  obtain ⟨hsm, hdiv⟩ := NumberField.LevelArith.sUnitsMaxRep_smooth_and_divisible (p := p) S hpS K
  obtain ⟨-, hA, hB⟩ := groupCohomology.kummer_degreeThree_exactness_continuousH2Sr_of_smooth_of_divisible (p := p) S K.fixingSubgroup.subtype
    (sUnitsMaxRep S K) hsm hdiv

  have hDIV : ∀ y : continuousH2Sr K.fixingSubgroup.subtype S (sUnitsMaxRep S K), ∃ z, y = p • z := by
    intro y
    refine BrauerDiv.exists_smul_eq_of_torsion p ?_ y (groupCohomology.exists_nsmul_eq_zero_continuousH2Sr _ S _ y)
    intro y' hy'
    obtain ⟨invQ, hinj, hrange, -⟩ := groupCohomology.exists_natural_localInv_pPrimary_continuousH2Sr_sUnitsMax S hpS K hK h4
    obtain ⟨kk, hkk⟩ := hy'
    have hmem : y' ∈ Submodule.torsion' ℤ (continuousH2Sr K.fixingSubgroup.subtype S (sUnitsMaxRep S K)) (Submonoid.powers (p : ℤ)) :=
      (Submodule.mem_torsion'_iff _ _).mpr ⟨⟨(p : ℤ) ^ kk, kk, rfl⟩, show ((p : ℤ) ^ kk) • y' = 0 by
        rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]; exact hkk⟩
    obtain ⟨t', ht'⟩ := BrauerDiv.exists_smul_eq p invQ hinj hrange ⟨y', hmem⟩
    exact ⟨t', congrArg Subtype.val ht'⟩

  let uT : (Fin 3 → ↥K.fixingSubgroup) → repTorsionP p (sUnitsMaxRep S K) := fun t => φ.inv.hom (u t)
  obtain ⟨F₀, hF₀, hu₀⟩ := hlc
  have huT_lc : ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧
      ∀ g s : Fin 3 → ↥K.fixingSubgroup, (∀ i, K.fixingSubgroup.subtype (s i) ∈ F.fixingSubgroup) → uT (g * s) = uT g :=
    ⟨F₀, hF₀, fun g s hs => by show φ.inv.hom (u (g * s)) = φ.inv.hom (u g); rw [hu₀ g s hs]⟩
  have hdu : ((inhomogeneousCochains ((Rep.trivial (ZMod p) ↥K.fixingSubgroup (ZMod p)).twist ((cycloChar p).comp K.fixingSubgroup.subtype))).d 3 4).hom u = 0 := by
    rw [d_twist_trivial_eq _ hχ, hcoc]
  have huT_coc : ((inhomogeneousCochains (repTorsionP p (sUnitsMaxRep S K))).d 3 4).hom uT = 0 := by
    show ((inhomogeneousCochains (repTorsionP p (sUnitsMaxRep S K))).d 3 4).hom (fun t => φ.inv.hom (u t)) = 0
    rw [d_comp φ.inv u, hdu]
    funext t
    exact map_zero _

  have hval_lc : ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧
      ∀ g s : Fin 3 → ↥K.fixingSubgroup,
        (∀ i, ((s i : ↥K.fixingSubgroup) : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) ∈ F.fixingSubgroup) → valF _ p uT (g * s) = valF _ p uT g := by
    obtain ⟨F, hF, h⟩ := huT_lc
    exact ⟨F, hF, fun g s hs => by show ((uT (g * s) : repTorsionP p (sUnitsMaxRep S K)) : sUnitsMaxRep S K) = _; rw [h g s hs]⟩
  have hval_coc : ((inhomogeneousCochains (sUnitsMaxRep S K)).d 3 4).hom (valF _ p uT) = 0 := by
    rw [← valF_d, huT_coc]; rfl
  have htor : ∃ (kk : ℕ) (w₀ : (Fin 2 → ↥K.fixingSubgroup) → sUnitsMaxRep S K),
      (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧
        ∀ g s : Fin 2 → ↥K.fixingSubgroup,
          (∀ i, ((s i : ↥K.fixingSubgroup) : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) ∈ F.fixingSubgroup) → w₀ (g * s) = w₀ g) ∧
      ((inhomogeneousCochains (sUnitsMaxRep S K)).d 2 3).hom w₀ = (p ^ kk : ℤ) • valF _ p uT := by
    refine ⟨1, 0, ⟨⊥, IntermediateField.isUnramifiedOutside_bot S, fun _ _ _ => rfl⟩, ?_⟩
    rw [map_zero]
    funext v
    symm
    show (p ^ 1 : ℤ) • ((uT v : repTorsionP p (sUnitsMaxRep S K)) : sUnitsMaxRep S K) = 0
    rw [pow_one]
    have hv := (Submodule.mem_torsionBy_iff (p : ℤ) _).mp (uT v).2
    exact hv
  obtain ⟨w₁, hw₁lc, hw₁⟩ := groupCohomology.exists_isLevelConstant_d_two_three_eq_of_pPow_smul_sUnitsMax S hpS K hK h4
    (valF _ p uT) hval_lc hval_coc htor

  obtain ⟨c, b, e, hlcbe, hpb, hdec⟩ := (hB uT huT_lc huT_coc).mp ⟨w₁, hw₁lc, hw₁⟩
  obtain ⟨F₁, hF₁, h₁⟩ := hlcbe

  obtain ⟨e', he'lc, hde'⟩ := (hA c b ⟨F₁, hF₁, fun g s hs => (h₁ g s hs).1⟩ hpb).mpr (hDIV _)

  have hT : ((inhomogeneousCochains (repTorsionP p (sUnitsMaxRep S K))).d 2 3).hom (e' + e) = uT := by
    apply valF_injective (sUnitsMaxRep S K) p
    rw [valF_d]
    have : valF (sUnitsMaxRep S K) p (e' + e) = valF _ p e' + valF _ p e := rfl
    rw [this, map_add, ← hde', ← hdec]

  refine ⟨fun t => φ.hom.hom ((e' + e) t), ?_, ?_⟩
  · obtain ⟨F₂, hF₂, h₂⟩ := he'lc
    refine ⟨F₁ ⊔ F₂, hF₁.sup hF₂, fun g s hs => ?_⟩
    have hs₁ : ∀ i, K.fixingSubgroup.subtype (s i) ∈ F₁.fixingSubgroup := fun i => IntermediateField.fixingSubgroup_antitone le_sup_left (hs i)
    have hs₂ : ∀ i, K.fixingSubgroup.subtype (s i) ∈ F₂.fixingSubgroup := fun i => IntermediateField.fixingSubgroup_antitone le_sup_right (hs i)
    show φ.hom.hom ((e' + e) (g * s)) = φ.hom.hom ((e' + e) g)
    rw [Pi.add_apply, Pi.add_apply, (h₁ g s hs₁).2, h₂ g s hs₂]
  · rw [← d_twist_trivial_eq _ hχ, d_comp φ.hom (e' + e), hT]
    funext t
    exact iso_hom_inv_apply φ (u t)

end S_groupCohomology_exists_isLevelConstant_d_two_three_eq_trivial_of_cycloChar_eq_one
end P2MW
export P2MW.S_groupCohomology_exists_isLevelConstant_d_two_three_eq_trivial_of_cycloChar_eq_one (solution)
