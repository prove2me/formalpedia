-- Prove2me | solution 1 for groupCohomology.exists_natural_localInv_torsionBy_continuousH2Sr_sUnitsMax
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/63ef1070-6585-5a72-be43-5093a05121bb

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_NumberField_SelmerRepModP
import Definitions.Def_NumberField_SUnitsMax
import Theorems.Thm_groupCohomology_exists_natural_localInv_pPrimary_continuousH2Sr_sUnitsMax
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_exists_natural_localInv_torsionBy_continuousH2Sr_sUnitsMax
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
p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Module CategoryTheory.Limits CategoryTheory.MonoidalCategory.Limits groupCohomology ExtCitation NumberField.LevelArith"
open scoped Classical NumberField.LevelArith TensorProduct Pointwise

namespace BrauerRed

variable (p : ℕ) [hp : Fact p.Prime]

noncomputable def ψℤ : ℤ →+ AddCircle (1 : ℚ) where
  toFun n := ((n : ℚ) / p : ℚ)
  map_zero' := by simp
  map_add' a b := by push_cast; rw [add_div]; rfl

omit hp in
theorem ψℤ_apply (n : ℤ) : ψℤ p n = (((n : ℚ) / p : ℚ) : AddCircle (1 : ℚ)) := rfl

theorem ψℤ_p : ψℤ p (p : ℤ) = 0 := by
  rw [ψℤ_apply, Int.cast_natCast, div_self (Nat.cast_ne_zero.mpr hp.out.ne_zero)]
  exact (AddCircle.coe_eq_zero_iff (1 : ℚ)).mpr ⟨1, by simp⟩

noncomputable def ψ : ZMod p →+ AddCircle (1 : ℚ) :=
  ZMod.lift p ⟨ψℤ p, ψℤ_p p⟩

theorem ψ_intCast (n : ℤ) : ψ p (n : ZMod p) = (((n : ℚ) / p : ℚ) : AddCircle (1 : ℚ)) := by
  rw [ψ, ZMod.lift_coe]; rfl

theorem ψ_injective : Function.Injective (ψ p) := by
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨n, rfl⟩ := ZMod.intCast_surjective a
  rw [ψ_intCast, AddCircle.coe_eq_zero_iff] at ha
  obtain ⟨m, hm⟩ := ha
  rw [zsmul_eq_mul, mul_one] at hm
  have h1 : (n : ℚ) = m * p := by rw [hm, div_mul_cancel₀ _ hp0]
  have h2 : n = m * p := by exact_mod_cast h1
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd n p).mpr ⟨m, by rw [h2, mul_comm]⟩

theorem exists_ψ_eq_of_smul_eq_zero (x : AddCircle (1 : ℚ)) (hx : (p : ℤ) • x = 0) : ∃ n : ZMod p, ψ p n = x := by
  induction x using QuotientAddGroup.induction_on with
  | H r =>
    have h1 : (((p : ℤ) • r : ℚ) : AddCircle (1 : ℚ)) = 0 := by rw [← hx]; rfl
    rw [AddCircle.coe_eq_zero_iff] at h1
    obtain ⟨m, hm⟩ := h1
    have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
    refine ⟨(m : ZMod p), ?_⟩
    rw [ψ_intCast]
    congr 1
    rw [zsmul_eq_mul, mul_one, zsmul_eq_mul, Int.cast_natCast] at hm
    rw [hm, mul_comm, mul_div_assoc, div_self hp0, mul_one]

theorem smul_ψ (n : ZMod p) : (p : ℤ) • ψ p n = 0 := by
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  obtain ⟨k, rfl⟩ := ZMod.intCast_surjective n
  rw [ψ_intCast, ← AddCircle.coe_zsmul, zsmul_eq_mul, AddCircle.coe_eq_zero_iff]
  exact ⟨k, by rw [zsmul_eq_mul, mul_one, Int.cast_natCast, mul_comm, div_mul_cancel₀ _ hp0]⟩

theorem pow_smul_ψ (k : ℕ) (hk : k ≠ 0) (n : ZMod p) : (p ^ k : ℤ) • ψ p n = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  rw [pow_succ, mul_smul, smul_ψ, smul_zero]

theorem restrict {A T : Type} [AddCommGroup A] [Module ℤ A] [Module (ZMod p) A] [AddCommMonoid T] [Module ℤ T] {ι : Type}
    (invQ : T →ₗ[ℤ] (ι → AddCircle (1 : ℚ))) (hinj : Function.Injective invQ)
    (hrange : ∀ f, f ∈ LinearMap.range invQ ↔ (∀ w, ∃ k : ℕ, (p ^ k : ℤ) • f w = 0) ∧ ∑ᶠ w, f w = 0)
    (j : A →ₗ[ℤ] T) (hj : Function.Injective j)
    (hA : ∀ a w, (p : ℤ) • invQ (j a) w = 0)
    (hT : ∀ t, (∀ w, (p : ℤ) • invQ t w = 0) → ∃ a, j a = t) :
    ∃ inv : A →ₗ[ZMod p] (ι → ZMod p),
      Function.Injective inv ∧ (∀ f, f ∈ LinearMap.range inv ↔ ∑ᶠ w, f w = 0) ∧
      ∀ a w, ψ p (inv a w) = invQ (j a) w := by
  classical
  have hex : ∀ a w, ∃ n : ZMod p, ψ p n = invQ (j a) w := fun a w => exists_ψ_eq_of_smul_eq_zero p _ (hA a w)
  choose ivf hivf using hex
  have hivf_add : ∀ a b, ivf (a + b) = ivf a + ivf b := by
    intro a b; funext w
    apply ψ_injective p
    simp only [hivf, Pi.add_apply, map_add]
  have hivf_zero : ivf 0 = 0 := by
    funext w; apply ψ_injective p
    simp only [hivf, Pi.zero_apply, map_zero]
  let invA : A →+ (ι → ZMod p) := { toFun := ivf, map_zero' := hivf_zero, map_add' := hivf_add }
  let inv : A →ₗ[ZMod p] (ι → ZMod p) := invA.toZModLinearMap p
  have hinv : ∀ a w, ψ p (inv a w) = invQ (j a) w := fun a w => hivf a w
  refine ⟨inv, ?_, ?_, hinv⟩
  ·
    intro a b hab
    apply hj; apply hinj
    funext w
    rw [← hinv, ← hinv, hab]
  ·
    intro f
    constructor
    · rintro ⟨a, rfl⟩
      obtain ⟨-, hsum⟩ := (hrange (invQ (j a))).mp ⟨j a, rfl⟩
      have hfun : (fun w => ψ p (inv a w)) = invQ (j a) := funext fun w => hinv a w
      rw [← hfun] at hsum
      apply ψ_injective p
      rw [map_zero]
      by_cases hfin : (Function.support fun w => inv a w).Finite
      · rw [AddMonoidHom.map_finsum (ψ p) hfin]; exact hsum
      · rw [finsum_of_infinite_support hfin, map_zero]
    · intro hsum
      have hg : (fun w => ψ p (f w)) ∈ LinearMap.range invQ := by
        rw [hrange]
        refine ⟨fun w => ⟨1, ?_⟩, ?_⟩
        · show (p ^ 1 : ℤ) • ψ p (f w) = 0
          rw [pow_one]; exact smul_ψ p (f w)
        · show ∑ᶠ w, ψ p (f w) = 0
          by_cases hfin : (Function.support f).Finite
          · rw [← AddMonoidHom.map_finsum (ψ p) hfin, hsum, map_zero]
          · have hs : (Function.support fun w => ψ p (f w)) = Function.support f := by
              ext w; simp only [Function.mem_support, ne_eq, map_eq_zero_iff (ψ p) (ψ_injective p)]
            exact finsum_of_infinite_support (by rw [hs]; exact hfin)
      obtain ⟨t, ht⟩ := hg
      have hpt : ∀ w, (p : ℤ) • invQ t w = 0 := fun w => by
        rw [ht]; exact smul_ψ p (f w)
      obtain ⟨a, rfl⟩ := hT t hpt
      refine ⟨a, ?_⟩
      funext w
      apply ψ_injective p
      rw [hinv, ht]

end BrauerRed

set_option maxHeartbeats 6400000 in

theorem solution
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hL : L.IsUnramifiedOutside S) [FiniteDimensional ℚ ↥L]
    (h4 : p = 2 → ∃ i ∈ L, i ^ 2 = -1) :
    ∃ inv : ↥(Submodule.torsionBy ℤ (continuousH2Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L)) (p : ℤ)) →ₗ[ZMod p] (↥(placesOverPrimes ↥L (S : Set Nat.Primes)) → ZMod p),
      Function.Injective inv ∧ (∀ f, f ∈ LinearMap.range inv ↔ ∑ᶠ w, f w = 0) ∧
      ∀ (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (τ : ↥L ≃ₐ[ℚ] ↥L), (∀ y : ↥L, σ (y : AlgebraicClosure ℚ) = ((τ y : ↥L) : AlgebraicClosure ℚ)) →
        ∀ (a a' : ↥(Submodule.torsionBy ℤ (continuousH2Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L)) (p : ℤ))) (w w' : ↥(levelCocyclesSr₂ L.fixingSubgroup.subtype S (sUnitsMaxRep S L))),
          (a : (continuousH2Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L))) = continuousH2Srπ L.fixingSubgroup.subtype S _ w → (a' : (continuousH2Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L))) = continuousH2Srπ L.fixingSubgroup.subtype S _ w' →
          (∀ s t s' t' : ↥L.fixingSubgroup, σ⁻¹ * (s : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) * σ = s' → σ⁻¹ * (t : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) * σ = t' →
            sUnitsMaxRep.val S L ((w' : ↥L.fixingSubgroup × ↥L.fixingSubgroup → (sUnitsMaxRep S L)) (s, t)) =
              σ • sUnitsMaxRep.val S L ((w : ↥L.fixingSubgroup × ↥L.fixingSubgroup → (sUnitsMaxRep S L)) (s', t'))) →
          ∀ (v v' : ↥(placesOverPrimes ↥L (S : Set Nat.Primes))), (∀ y : ↥L, (v'.1).valuation ↥L (τ y) = (v.1).valuation ↥L y) →
            inv a' v' = inv a v := by
  obtain ⟨invQ, hinj, hrange, hnat⟩ :=
    groupCohomology.exists_natural_localInv_pPrimary_continuousH2Sr_sUnitsMax S hpS L hL h4

  have hle : Submodule.torsionBy ℤ (continuousH2Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L)) (p : ℤ) ≤
      Submodule.torsion' ℤ (continuousH2Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L)) (Submonoid.powers (p : ℤ)) :=
    fun x hx => (Submodule.mem_torsion'_iff _ _).mpr ⟨⟨(p : ℤ), Submonoid.mem_powers _⟩, (Submodule.mem_torsionBy_iff _ _).mp hx⟩
  let j : ↥(Submodule.torsionBy ℤ (continuousH2Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L)) (p : ℤ)) →ₗ[ℤ]
      ↥(Submodule.torsion' ℤ (continuousH2Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L)) (Submonoid.powers (p : ℤ))) :=
    Submodule.inclusion hle

  let invw : ↥(placesOverPrimes ↥L (S : Set Nat.Primes)) →
      (↥(Submodule.torsionBy ℤ (continuousH2Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L)) (p : ℤ)) →ₗ[ℤ] AddCircle (1 : ℚ)) :=
    fun w => (LinearMap.proj w).comp (invQ.comp j)
  have hinvw : ∀ w a, invw w a = invQ (j a) w := fun _ _ => rfl
  have hpa0 : ∀ a : ↥(Submodule.torsionBy ℤ (continuousH2Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L)) (p : ℤ)), (p : ℤ) • a = 0 :=
    fun a => Subtype.ext (by rw [Submodule.coe_smul, Submodule.coe_zero]; exact (Submodule.mem_torsionBy_iff _ _).mp a.2)

  have hA : ∀ (a : ↥(Submodule.torsionBy ℤ (continuousH2Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L)) (p : ℤ)))
      (w : ↥(placesOverPrimes ↥L (S : Set Nat.Primes))), (p : ℤ) • invQ (j a) w = 0 := by
    intro a w
    rw [← hinvw, ← map_smul (invw w) (p : ℤ) a, hpa0 a, map_zero]

  have hT : ∀ t : ↥(Submodule.torsion' ℤ (continuousH2Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L)) (Submonoid.powers (p : ℤ))),
      (∀ w, (p : ℤ) • invQ t w = 0) → ∃ a, j a = t := by
    intro t ht
    have h1 : invQ ((p : ℤ) • t) = 0 :=
      funext fun w => ((congrFun (map_smul invQ (p : ℤ) t) w).trans (Pi.smul_apply _ _ _)).trans (ht w)
    have hpt := hinj (h1.trans (map_zero invQ).symm)
    have hmem : (t : continuousH2Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L)) ∈
        Submodule.torsionBy ℤ (continuousH2Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L)) (p : ℤ) :=
      (Submodule.mem_torsionBy_iff _ _).mpr (congrArg Subtype.val hpt)
    exact ⟨⟨_, hmem⟩, Subtype.ext rfl⟩
  obtain ⟨inv, h1, h2, h3⟩ := BrauerRed.restrict p invQ hinj hrange j (Submodule.inclusion_injective hle) hA hT
  refine ⟨inv, h1, h2, ?_⟩

  intro σ τ hστ a a' w w' ha ha' hrel v v' hv
  apply BrauerRed.ψ_injective p
  exact (h3 a' v').trans ((hnat σ τ hστ (j a) (j a') w w' ha ha' hrel v v' hv).trans (h3 a v).symm)

end S_groupCohomology_exists_natural_localInv_torsionBy_continuousH2Sr_sUnitsMax
end P2MW
export P2MW.S_groupCohomology_exists_natural_localInv_torsionBy_continuousH2Sr_sUnitsMax (solution)
