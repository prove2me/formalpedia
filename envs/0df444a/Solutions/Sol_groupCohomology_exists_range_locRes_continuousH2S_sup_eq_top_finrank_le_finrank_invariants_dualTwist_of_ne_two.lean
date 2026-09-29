-- Prove2me | solution 1 for groupCohomology.exists_range_locRes_continuousH2S_sup_eq_top_finrank_le_finrank_invariants_dualTwist_of_ne_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/4e330f9e-0463-582f-8a9d-9f185cfcfc00

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Theorems.Thm_groupCohomology_exists_range_locRes_continuousH2S_sup_eq_top_of_surjective_of_ne_two
import Theorems.Thm_groupCohomology_exists_isUnramifiedOutside_forall_apply_eq_one_of_smooth
import Theorems.Thm_IntermediateField_IsUnramifiedOutside_normalClosure
import Theorems.Thm_groupCohomology_exists_level_ofChar_cycloChar_comp
import Theorems.Thm_groupCohomology_exists_forall_locRes_continuousH2S_coind_eq_add_sum_of_exists_sq_eq_neg_one
import Definitions.Def_GroupCohomology_LevelSubgroup
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_exists_range_locRes_continuousH2S_sup_eq_top_finrank_le_finrank_invariants_dualTwist_of_ne_two
p2m_attr_erase "instance" "ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete groupCohomology.Kummer.instMulDistribMulActionRootsOfUnity M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion NumberField.AdelicHaar.locallyCompactSpace_adeleRing NumberField.AdelicHaar.finite_residueField_adicCompletionIntegers NumberField.AdelicHaar.locallyCompactSpace_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_finiteAdeleRing NumberField.AdelicHaar.compactSpace_adicCompletionIntegers NumberField.AdelicHaar.t2Space_finiteAdeleRing NumberField.AdelicHaar.t2Space_matrix_adeleRing NumberField.AdelicHaar.t2Space_adeleRing NumberField.AdelicHaar.fact_isOpen_adicCompletionIntegers NumberField.AdelicHaar.t2Space_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_matrix_adeleRing"
p2m_attr_erase "instance" "NumberField.AdelicHaar.t2Space_infiniteAdeleRing NumberField.AdelicHaar.properSpace_adicCompletion M4aHerbrand.Bridge.instT2SpaceAdeleRing LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite Deep.NTSupply.instNormalRayClassSubgroup instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal AlgebraicClosure.Rat.isGalois groupCohomology.instMulDistribMulActionGaloisSUnits NumberField.LevelArith.instCommGroupUnitsModPow"
p2m_attr_erase "simp" "groupCohomology.cup_apply groupCohomology.cupCochain_apply groupCohomology.H1desc_H1π groupCohomology.unitsInflate₁_apply groupCohomology.unitsInflate₂_apply ExtCitation.LocalLevel.coe_smul_OO WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply groupCohomology.Kummer.coe_kummerCocycleRoots groupCohomology.Kummer.mem_powerSubgroup_iff groupCohomology.Kummer.val_smul_units groupCohomology.Kummer.kummerHom_apply groupCohomology.Kummer.coe_smul_rootsOfUnity IsLocalRing.principalUnits_zero M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk M4aHerbrand.IdeleGaloisDescent.classAct_mk M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl NumberField.SUnits.val_zsmul NumberField.SUnits.val_add M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul"
p2m_attr_erase "simp" "M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq M4aHerbrand.Bridge.finiteConorm_apply SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun"
p2m_attr_erase "simp" "SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply"
p2m_attr_erase "simp" "Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec"
p2m_attr_erase "simp" "AutomorphicForm.satakePow_one TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec groupCohomology.coe_continuousH1SrMap_apply groupCohomology.continuousH2SrMap_continuousH2Srπ groupCohomology.coe_levelCocyclesSr₂Map groupCohomology.coe_smul_galoisSUnits groupCohomology.galoisSUnitsToUnits_apply NumberField.LevelArith.coe_levelFieldEquiv NumberField.LevelArith.modP_apply_mk NumberField.LevelArith.coe_levelFieldEquiv_symm NumberField.LevelArith.torsionP_apply_coe NumberField.LevelArith.repTorsionPMap_hom_apply_coe NumberField.LevelArith.toZMod_apply NumberField.LevelArith.repModPMap_hom_mk NumberField.LevelArith.smul_mk NumberField.LevelArith.selmerRepInt_ρ_apply NumberField.LevelArith.selmerRepField_ρ_apply NumberField.LevelArith.unitsModPowMap_mk groupCohomology.continuousH2Inflation_H2π groupCohomology.levelInflate₂_apply groupCohomology.coe_levelInflateCocycles₂ groupCohomology.levelInflate₁_apply"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
open CategoryTheory Module groupCohomology ExtCitation

noncomputable section

local instance P2M5b7Odd.isAlgebraicQbar : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) :=
  AlgebraicClosure.isAlgebraic ℚ
local instance P2M5b7Odd.isAlgClosureQbar : IsAlgClosure ℚ (AlgebraicClosure ℚ) :=
  ⟨inferInstance, inferInstance⟩
local instance P2M5b7Odd.isGaloisQbar : IsGalois ℚ (AlgebraicClosure ℚ) :=
  IsAlgClosure.isGalois ℚ (AlgebraicClosure ℚ)

namespace P2M5b7Odd

local notation "Γ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

section Cyclo

variable (p : ℕ) [Fact p.Prime]

lemma not_liesOverPrime_of_ne {A : ValuationSubring (AlgebraicClosure ℚ)} {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (hA : A.LiesOverPrime q) : ¬ A.LiesOverPrime p := by
  intro hAp
  have hcop : IsCoprime (q : A) (p : A) := by
    have h := (Nat.coprime_primes hq (Fact.out : p.Prime)).2 hqp
    have h' : IsCoprime (q : ℤ) (p : ℤ) := Nat.isCoprime_iff_coprime.2 h
    simpa using h'.intCast (R := A)
  have hqm : (q : A) ∈ IsLocalRing.maximalIdeal A := by
    have : ((q : A) : AlgebraicClosure ℚ) ∈ A.nonunits := by simpa [ValuationSubring.LiesOverPrime] using hA
    exact A.coe_mem_nonunits_iff.mp this
  have hpm : (p : A) ∈ IsLocalRing.maximalIdeal A := by
    have : ((p : A) : AlgebraicClosure ℚ) ∈ A.nonunits := by simpa [ValuationSubring.LiesOverPrime] using hAp
    exact A.coe_mem_nonunits_iff.mp this
  obtain ⟨a, b, hab⟩ := hcop
  have h1 : (1 : A) ∈ IsLocalRing.maximalIdeal A := by
    rw [← hab]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hqm) (Ideal.mul_mem_left _ _ hpm)
  exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top ((Ideal.eq_top_iff_one _).2 h1)

theorem inertia_apply_eq_of_pow_eq_one {A : ValuationSubring (AlgebraicClosure ℚ)} {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (hA : A.LiesOverPrime q) {τ : Γ} (hτ : τ ∈ A.inertiaSubgroupIn ℚ)
    {ζ : AlgebraicClosure ℚ} (hζ : ζ ^ p = 1) : τ ζ = ζ := by
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_le

  have hζA : ζ ∈ A := by
    rw [← ValuationSubring.valuation_le_one_iff]
    have hv : A.valuation ζ ^ p = 1 := by rw [← map_pow, hζ, map_one]
    exact ((pow_eq_one_iff_of_nonneg zero_le' (Fact.out : p.Prime).ne_zero).mp hv).le
  rw [ValuationSubring.inertiaSubgroupIn, Subgroup.mem_map] at hτ
  obtain ⟨τ', hτ', rfl⟩ := hτ
  set z : ↥A := ⟨ζ, hζA⟩
  have hzp : z ^ p = 1 := Subtype.ext (by simp [z, hζ])
  have hres : IsLocalRing.residue A (τ' • z) = IsLocalRing.residue A z := by
    rw [IsLocalRing.ResidueField.residue_smul]
    rw [ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker] at hτ'
    have := congrArg (fun e => (e : IsLocalRing.ResidueField ↥A ≃+* _) (IsLocalRing.residue A z)) hτ'
    simpa using this

  set η : ↥A := (τ' • z) * z ^ (p - 1)
  have hηp : η ^ p = 1 := by
    rw [mul_pow, ← smul_pow', hzp, smul_one, one_mul, ← pow_mul, mul_comm, pow_mul, hzp, one_pow]
  have hηres : IsLocalRing.residue A η = 1 := by
    rw [map_mul, hres, ← map_mul, ← pow_succ', Nat.sub_add_cancel hp1, hzp, map_one]

  have hη1 : η = 1 := by
    by_contra hne
    have hgeom : (∑ i ∈ Finset.range p, η ^ i) = 0 := by
      have h := mul_geom_sum η p
      rw [hηp, sub_self] at h
      exact (mul_eq_zero.1 h).resolve_left (sub_ne_zero.2 hne)
    have hres_sum : IsLocalRing.residue A (∑ i ∈ Finset.range p, η ^ i) = (p : IsLocalRing.ResidueField ↥A) := by
      rw [map_sum]
      simp [map_pow, hηres]
    rw [hgeom, map_zero] at hres_sum
    have hpm : (p : ↥A) ∈ IsLocalRing.maximalIdeal ↥A := by
      rw [← IsLocalRing.residue_eq_zero_iff]
      rw [map_natCast]; exact hres_sum.symm
    have hAp : A.LiesOverPrime p := by
      change ((p : AlgebraicClosure ℚ)) ∈ A.nonunits
      have : ((p : ↥A) : AlgebraicClosure ℚ) ∈ A.nonunits := A.coe_mem_nonunits_iff.mpr hpm
      simpa using this
    exact not_liesOverPrime_of_ne p hq hqp hA hAp

  have key : τ' • z = z := by
    calc τ' • z = (τ' • z) * z ^ (p - 1) * z := by
          rw [mul_assoc, ← pow_succ, Nat.sub_add_cancel hp1, hzp, mul_one]
      _ = z := by rw [show (τ' • z) * z ^ (p - 1) = η from rfl, hη1, one_mul]
  exact congrArg Subtype.val key

theorem cycloChar_eq_one_of_mem_inertia {A : ValuationSubring (AlgebraicClosure ℚ)} {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (hA : A.LiesOverPrime q) {τ : Γ} (hτ : τ ∈ A.inertiaSubgroupIn ℚ) : cycloChar p τ = 1 := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI : Fact (1 < p) := ⟨(Fact.out : p.Prime).one_lt⟩
  change modularCyclotomicCharacter (AlgebraicClosure ℚ) (card_rootsOfUnity_eq_self p)
      (τ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) = 1
  refine Units.ext ?_
  rw [Units.val_one]
  refine (modularCyclotomicCharacter.unique (AlgebraicClosure ℚ) (card_rootsOfUnity_eq_self p)
    (τ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) (c := 1) fun t ht => ?_).symm
  rw [ZMod.val_one, pow_one]
  have hζ : ((t : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) ^ p = 1 := by
    rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity p t).1 ht, Units.val_one]
  exact inertia_apply_eq_of_pow_eq_one p hq hqp hA hτ hζ

end Cyclo

section SqrtNegOne

theorem inertia_apply_eq_of_sq_eq_neg_one {A : ValuationSubring (AlgebraicClosure ℚ)} {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) (hA : A.LiesOverPrime q) {τ : Γ} (hτ : τ ∈ A.inertiaSubgroupIn ℚ)
    {i : AlgebraicClosure ℚ} (hi : i ^ 2 = -1) : τ i = i := by

  have hi4 : i ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hi]; norm_num
  have hiA : i ∈ A := by
    rw [← ValuationSubring.valuation_le_one_iff]
    have hv : A.valuation i ^ 4 = 1 := by rw [← map_pow, hi4, map_one]
    exact ((pow_eq_one_iff_of_nonneg zero_le' (by norm_num : (4 : ℕ) ≠ 0)).mp hv).le
  rw [ValuationSubring.inertiaSubgroupIn, Subgroup.mem_map] at hτ
  obtain ⟨τ', hτ', rfl⟩ := hτ
  set z : ↥A := ⟨i, hiA⟩
  have hz2 : z ^ 2 = -1 := Subtype.ext (by simp [z, hi])
  have hres : IsLocalRing.residue A (τ' • z) = IsLocalRing.residue A z := by
    rw [IsLocalRing.ResidueField.residue_smul]
    rw [ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker] at hτ'
    have := congrArg (fun e => (e : IsLocalRing.ResidueField ↥A ≃+* _) (IsLocalRing.residue A z)) hτ'
    simpa using this

  have hτz2 : (τ' • z) ^ 2 = -1 := by rw [← smul_pow', hz2, smul_neg, smul_one]
  have hor : τ' • z = z ∨ τ' • z = -z := by
    have h0 : (τ' • z - z) * (τ' • z + z) = 0 := by
      have : (τ' • z - z) * (τ' • z + z) = (τ' • z) ^ 2 - z ^ 2 := by ring
      rw [this, hτz2, hz2, sub_self]
    rcases mul_eq_zero.1 h0 with h | h
    · exact Or.inl (sub_eq_zero.1 h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  rcases hor with h | h
  · exact congrArg Subtype.val h
  · exfalso

    have h2z : IsLocalRing.residue A (2 * z) = 0 := by
      rw [two_mul, map_add]
      nth_rewrite 1 [← hres]
      rw [h, map_neg, neg_add_cancel]
    have hm : (2 * z : ↥A) ∈ IsLocalRing.maximalIdeal ↥A := (IsLocalRing.residue_eq_zero_iff _).1 h2z
    have h4m : (4 : ↥A) ∈ IsLocalRing.maximalIdeal ↥A := by
      have hmul : (2 * z) * (2 * z) ∈ IsLocalRing.maximalIdeal ↥A := Ideal.mul_mem_left _ _ hm
      have hcalc : (2 * z) * (2 * z) = -4 := by
        have : (2 * z) * (2 * z) = 4 * z ^ 2 := by ring
        rw [this, hz2]; ring
      rw [hcalc] at hmul
      simpa using (Ideal.neg_mem_iff _).1 hmul
    have h2m : (2 : ↥A) ∈ IsLocalRing.maximalIdeal ↥A := by
      have h22 : (2 : ↥A) * 2 ∈ IsLocalRing.maximalIdeal ↥A := by
        have : (2 : ↥A) * 2 = 4 := by norm_num
        rw [this]; exact h4m
      exact ((IsLocalRing.maximalIdeal.isMaximal ↥A).isPrime.mem_or_mem h22).elim id id
    have hA2 : A.LiesOverPrime 2 := by
      change (((2 : ℕ) : AlgebraicClosure ℚ)) ∈ A.nonunits
      have : (((2 : ℕ) : ↥A) : AlgebraicClosure ℚ) ∈ A.nonunits :=
        A.coe_mem_nonunits_iff.mpr (by simpa using h2m)
      have e2 : (((2 : ℕ) : ↥A) : AlgebraicClosure ℚ) = ((2 : ℕ) : AlgebraicClosure ℚ) := by norm_cast
      rw [e2] at this
      exact this
    exact not_liesOverPrime_of_ne 2 hq hq2 hA hA2

lemma isUnramifiedOutside_adjoin_of_sq_eq_neg_one (S : Finset Nat.Primes) (h2S : (⟨2, Nat.prime_two⟩ : Nat.Primes) ∈ S)
    {i : AlgebraicClosure ℚ} (hi : i ^ 2 = -1) :
    (IntermediateField.adjoin ℚ {i}).IsUnramifiedOutside S := by
  have hint : IsIntegral ℚ i := (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) i).isIntegral
  refine ⟨IntermediateField.adjoin.finiteDimensional hint, fun q hq A hA τ hτ => ?_⟩
  have hq2 : (q : ℕ) ≠ 2 := by
    intro h
    apply hq
    have : q = (⟨2, Nat.prime_two⟩ : Nat.Primes) := Subtype.ext h
    rw [this]; exact h2S
  have hfix : τ i = i := inertia_apply_eq_of_sq_eq_neg_one q.2 hq2 hA hτ hi
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  have hle : IntermediateField.adjoin ℚ {i} ≤ IntermediateField.fixedField (MulAction.stabilizer Γ i) := by
    rw [IntermediateField.adjoin_simple_le_iff, IntermediateField.mem_fixedField_iff]
    intro f hf
    exact hf
  exact (IntermediateField.mem_fixedField_iff _ _).1 (hle hx) τ (MulAction.mem_stabilizer_iff.2 hfix)

end SqrtNegOne

section SLevel

variable {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
  (M : Rep (ZMod p) Γ) [FiniteDimensional (ZMod p) M]
  (hsm : ∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s ∈ F.fixingSubgroup, M.ρ s m = m)
  (hMur : ∀ q : Nat.Primes, q ∉ S → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
      A.LiesOverPrime (q : ℕ) → ∀ g ∈ A.inertiaSubgroupIn ℚ, M.ρ g = 1)

abbrev NQ (p : ℕ) [Fact p.Prime] : Rep (ZMod p) Γ := ofChar (k := ZMod p) (cycloChar p)

include hpS in

lemma exists_SLevel_cycloChar : ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧
    ∀ s ∈ F.fixingSubgroup, cycloChar p s = 1 := by

  have hsmχ : ∀ m : NQ p, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s ∈ F.fixingSubgroup, (NQ p).ρ s m = m := fun m => by
    obtain ⟨F, hF, h⟩ := exists_level_ofChar_cycloChar_comp (p := p) (MonoidHom.id Γ) m
    exact ⟨F, hF, fun s hs => h s hs⟩

  have hMurχ : ∀ q : Nat.Primes, q ∉ S → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
      A.LiesOverPrime (q : ℕ) → ∀ g ∈ A.inertiaSubgroupIn ℚ, (NQ p).ρ g = 1 := by
    intro q hq A hA g hg
    have hqp : (q : ℕ) ≠ p := by
      rintro h
      apply hq
      have : q = pPrime p := Subtype.ext h
      rw [this]; exact hpS
    have h1 := cycloChar_eq_one_of_mem_inertia p q.2 hqp hA hg
    refine LinearMap.ext fun x => ?_
    change ((cycloChar p g : (ZMod p)ˣ) : ZMod p) • x = x
    rw [h1, Units.val_one, one_smul]
  haveI : Module.Finite (ZMod p) (NQ p) := inferInstance
  obtain ⟨F, hF, h⟩ := exists_isUnramifiedOutside_forall_apply_eq_one_of_smooth S (NQ p) hsmχ hMurχ
  refine ⟨F, hF, fun s hs => ?_⟩
  have h1 := LinearMap.congr_fun (h s hs) (1 : ZMod p)
  change ((cycloChar p s : (ZMod p)ˣ) : ZMod p) • (1 : ZMod p) = 1 at h1
  rw [smul_eq_mul, mul_one] at h1
  exact Units.ext h1

include hpS hsm hMur in

lemma exists_galois_SLevel : ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), IsGalois ℚ F ∧
    F.IsUnramifiedOutside S ∧ (∀ s ∈ F.fixingSubgroup, M.ρ s = 1) ∧ (∀ s ∈ F.fixingSubgroup, cycloChar p s = 1) ∧
    (p = 2 → ∃ i ∈ F, i ^ 2 = -1) := by
  obtain ⟨F₁, hF₁, h₁⟩ := exists_isUnramifiedOutside_forall_apply_eq_one_of_smooth S M hsm hMur
  obtain ⟨F₂, hF₂, h₂⟩ := exists_SLevel_cycloChar S hpS

  obtain ⟨i, hi⟩ : ∃ i : AlgebraicClosure ℚ, i ^ 2 = -1 := IsAlgClosed.exists_pow_nat_eq (-1) (by norm_num)
  obtain ⟨F₃, hF₃, h₃⟩ : ∃ F₃ : IntermediateField ℚ (AlgebraicClosure ℚ), F₃.IsUnramifiedOutside S ∧
      (p = 2 → i ∈ F₃) := by
    by_cases hp : p = 2
    · refine ⟨IntermediateField.adjoin ℚ {i}, isUnramifiedOutside_adjoin_of_sq_eq_neg_one S ?_ hi,
        fun _ => IntermediateField.mem_adjoin_simple_self ℚ i⟩
      have : (⟨2, Nat.prime_two⟩ : Nat.Primes) = pPrime p := Subtype.ext (by simp [hp])
      rw [this]; exact hpS
    · exact ⟨⊥, IntermediateField.isUnramifiedOutside_bot S, fun h => absurd h hp⟩
  haveI := hF₁.1; haveI := hF₂.1; haveI := hF₃.1
  let F₀ : IntermediateField ℚ (AlgebraicClosure ℚ) := F₁ ⊔ F₂ ⊔ F₃
  have hF₀ : F₀.IsUnramifiedOutside S := (hF₁.sup hF₂).sup hF₃
  haveI : FiniteDimensional ℚ F₀ := hF₀.1
  let F : IntermediateField ℚ (AlgebraicClosure ℚ) := IntermediateField.normalClosure ℚ F₀ (AlgebraicClosure ℚ)
  have hF : F.IsUnramifiedOutside S := hF₀.normalClosure
  have hle : F₀ ≤ F := IntermediateField.le_normalClosure F₀
  have hU₁ : F.fixingSubgroup ≤ F₁.fixingSubgroup :=
    IntermediateField.fixingSubgroup_antitone ((le_sup_left.trans le_sup_left).trans hle)
  have hU₂ : F.fixingSubgroup ≤ F₂.fixingSubgroup :=
    IntermediateField.fixingSubgroup_antitone ((le_sup_right.trans le_sup_left).trans hle)
  have hle₃ : F₃ ≤ F := le_sup_right.trans hle
  refine ⟨F, ?_, hF, fun s hs => h₁ s (hU₁ hs), fun s hs => h₂ s (hU₂ hs), fun hp => ⟨i, hle₃ (h₃ hp), hi⟩⟩
  exact IsGalois.normalClosure ℚ F₀ (AlgebraicClosure ℚ)

end SLevel

section Coind

variable {p : ℕ} [Fact p.Prime] (U : Subgroup Γ) (M : Rep (ZMod p) Γ)

abbrev M₁ : Rep (ZMod p) Γ := Rep.coind U.subtype (Rep.res U.subtype M)

lemma M₁_apply_mul (f : M₁ U M) (u : ↥U) (x : Γ) : (f : Γ → M) ((u : Γ) * x) = M.ρ (u : Γ) ((f : Γ → M) x) :=
  f.2 u x

@[scoped simp] lemma M₁_ρ_apply (g : Γ) (f : M₁ U M) (x : Γ) : ((M₁ U M).ρ g f : Γ → M) x = (f : Γ → M) (x * g) := rfl

variable [U.FiniteIndex]

attribute [local instance] Fintype.ofFinite

def epsTerm (f : M₁ U M) : Γ ⧸ U → M :=
  Quotient.lift (fun g : Γ => M.ρ g ((f : Γ → M) g⁻¹)) (by
    intro a b hab'
    have hab : a⁻¹ * b ∈ U := QuotientGroup.leftRel_apply.mp hab'

    have hb : b = a * (a⁻¹ * b) := by group
    change M.ρ a ((f : Γ → M) a⁻¹) = M.ρ b ((f : Γ → M) b⁻¹)
    conv_rhs => rw [hb]
    rw [mul_inv_rev, map_mul, Module.End.mul_apply]
    have := M₁_apply_mul U M f ⟨(a⁻¹ * b)⁻¹, inv_mem hab⟩ a⁻¹
    simp only at this
    rw [this]
    change M.ρ a ((f : Γ → M) a⁻¹) = M.ρ a ((M.ρ (a⁻¹ * b) * M.ρ (a⁻¹ * b)⁻¹) ((f : Γ → M) a⁻¹))
    rw [← map_mul, mul_inv_cancel, map_one, Module.End.one_apply])

omit [U.FiniteIndex] in
@[scoped simp] lemma epsTerm_mk (f : M₁ U M) (g : Γ) : epsTerm U M f (QuotientGroup.mk g) = M.ρ g ((f : Γ → M) g⁻¹) := rfl

def eps : M₁ U M →ₗ[ZMod p] M where
  toFun f := ∑ c : Γ ⧸ U, epsTerm U M f c
  map_add' f f' := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    induction c using QuotientGroup.induction_on with
    | H g => simp [epsTerm_mk]
  map_smul' r f := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    induction c using QuotientGroup.induction_on with
    | H g => simp [epsTerm_mk]

lemma eps_apply (f : M₁ U M) : eps U M f = ∑ c : Γ ⧸ U, epsTerm U M f c := rfl

lemma eps_equivariant (g : Γ) (f : M₁ U M) : eps U M ((M₁ U M).ρ g f) = M.ρ g (eps U M f) := by
  classical
  rw [eps_apply, eps_apply, map_sum]

  refine Fintype.sum_equiv (MulAction.toPerm (g⁻¹ : Γ) : Equiv.Perm (Γ ⧸ U)) _ _ fun c => ?_
  induction c using QuotientGroup.induction_on with
  | H x =>
    change epsTerm U M ((M₁ U M).ρ g f) (QuotientGroup.mk x) = M.ρ g (epsTerm U M f (QuotientGroup.mk (g⁻¹ * x)))
    rw [epsTerm_mk, epsTerm_mk, M₁_ρ_apply, ← Module.End.mul_apply, ← map_mul, mul_inv_rev, inv_inv,
      mul_inv_cancel_left]

variable (hU : ∀ u ∈ U, M.ρ u = 1)

def deltaFun (m : M) : M₁ U M :=
  ⟨fun x => by classical exact if x ∈ U then m else 0, by
    classical
    intro u x
    change (if (u : Γ) * x ∈ U then m else 0) = M.ρ (u : Γ) (if x ∈ U then m else 0)
    by_cases hx : x ∈ U
    · rw [if_pos hx, if_pos (mul_mem u.2 hx), hU u u.2, Module.End.one_apply]
    · rw [if_neg hx, if_neg (fun h => hx (by simpa using mul_mem (inv_mem u.2) h)), map_zero]⟩

include hU in
omit [U.FiniteIndex] in
lemma deltaFun_apply (m : M) (x : Γ) : (deltaFun U M hU m : Γ → M) x = by classical exact if x ∈ U then m else 0 := rfl

include hU in

lemma eps_surjective : Function.Surjective (eps U M) := by
  classical
  intro m
  refine ⟨deltaFun U M hU m, ?_⟩
  rw [eps_apply, Finset.sum_eq_single (QuotientGroup.mk 1 : Γ ⧸ U)]
  · rw [epsTerm_mk, inv_one, deltaFun_apply, if_pos (one_mem U), map_one, Module.End.one_apply]
  · intro c _ hc
    induction c using QuotientGroup.induction_on with
    | H x =>
      rw [epsTerm_mk, deltaFun_apply, if_neg, map_zero]
      intro hx
      apply hc
      rw [QuotientGroup.eq]
      simpa using hx
  · intro h; exact absurd (Finset.mem_univ _) h

lemma finiteDimensional_M₁ [FiniteDimensional (ZMod p) M] : FiniteDimensional (ZMod p) (M₁ U M) := by
  classical
  let ev : M₁ U M →ₗ[ZMod p] (Γ ⧸ U → M) :=
    { toFun := fun f c => (f : Γ → M) (Quotient.out c)⁻¹
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
  have h1 := M₁_apply_mul U M f ⟨_, hu⟩ (Quotient.out c)⁻¹
  have h2 := M₁_apply_mul U M f' ⟨_, hu⟩ (Quotient.out c)⁻¹
  rw [hy, h1, h2, hf]

variable (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ F]

include hU in
omit [U.FiniteIndex] in

lemma hsm_M₁ [U.Normal] (hUF : U = F.fixingSubgroup) :
    ∀ f : M₁ U M, ∃ F' : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F' ∧
      ∀ s ∈ F'.fixingSubgroup, (M₁ U M).ρ s f = f := by
  intro f
  refine ⟨F, inferInstance, fun s hs => ?_⟩
  have hsU : s ∈ U := hUF ▸ hs
  apply Subtype.ext
  funext x
  rw [M₁_ρ_apply]
  have hconj : x * s * x⁻¹ ∈ U := Subgroup.Normal.conj_mem inferInstance s hsU x
  have := M₁_apply_mul U M f ⟨_, hconj⟩ x
  simp only at this
  rw [inv_mul_cancel_right] at this
  rw [this, hU _ hconj, Module.End.one_apply]

end Coind

section Supplement

variable {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (X : Rep (ZMod p) Γ)

def LocProd : Type :=
  ∀ q : ↥S, continuousH2 (extArithLoc S (Sum.inr q)) (Rep.res (extArithLoc S (Sum.inr q)) X)

scoped instance instAddCommGroupLocProd : AddCommGroup (LocProd S X) := Pi.addCommGroup

abbrev moduleLocProdRaw : Module (ZMod p)
    (∀ q : ↥S, continuousH2 (extArithLoc S (Sum.inr q)) (Rep.res (extArithLoc S (Sum.inr q)) X)) :=
  inferInstance

scoped instance instModuleLocProd : Module (ZMod p) (LocProd S X) := moduleLocProdRaw S X

def locPi : continuousH2S S X →ₗ[ZMod p] LocProd S X :=
  (LinearMap.pi fun q : ↥S => locRes₂S S X (extArithLoc S (Sum.inr q)) :
    continuousH2S S X →ₗ[ZMod p]
      ∀ q : ↥S, continuousH2 (extArithLoc S (Sum.inr q)) (Rep.res (extArithLoc S (Sum.inr q)) X))

def projq (q : ↥S) : LocProd S X →ₗ[ZMod p]
    continuousH2 (extArithLoc S (Sum.inr q)) (Rep.res (extArithLoc S (Sum.inr q)) X) where
  toFun z := z q
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma exists_submodule_supplement (n : ℕ)
    (w : Fin n → ∀ q : ↥S, continuousH2 (extArithLoc S (Sum.inr q)) (Rep.res (extArithLoc S (Sum.inr q)) X))
    (hn : n ≤ Module.finrank (ZMod p) (X.dualTwist (cycloChar p)).ρ.invariants)
    (hz : ∀ z : ∀ q : ↥S, continuousH2 (extArithLoc S (Sum.inr q)) (Rep.res (extArithLoc S (Sum.inr q)) X),
      ∃ (x : continuousH2S S X) (c : Fin n → ZMod p),
        locRes₂S S X (extArithLoc S (Sum.inl ())) x = 0 ∧
        ∀ q : ↥S, z q = locRes₂S S X (extArithLoc S (Sum.inr q)) x + ∑ i, c i • w i q) :
    ∃ W : Submodule (ZMod p)
        (∀ q : ↥S, continuousH2 (extArithLoc S (Sum.inr q)) (Rep.res (extArithLoc S (Sum.inr q)) X)),
      Module.Finite (ZMod p) W ∧
      Module.finrank (ZMod p) W ≤ Module.finrank (ZMod p) (X.dualTwist (cycloChar p)).ρ.invariants ∧
      (LinearMap.ker (locRes₂S S X (extArithLoc S (Sum.inl ())))).map
          (LinearMap.pi fun q : ↥S => locRes₂S S X (extArithLoc S (Sum.inr q))) ⊔ W = ⊤ := by
  classical
  let w' : Fin n → LocProd S X := w
  let W : Submodule (ZMod p) (LocProd S X) := Submodule.span (ZMod p) (Set.range w')
  have hWfin : Module.Finite (ZMod p) W := Module.Finite.span_of_finite _ (Set.finite_range w')
  have hWle : Module.finrank (ZMod p) W ≤ Module.finrank (ZMod p) (X.dualTwist (cycloChar p)).ρ.invariants :=
    ((finrank_range_le_card w').trans_eq (Fintype.card_fin n)).trans hn
  refine ⟨W, hWfin, hWle, ?_⟩
  change (LinearMap.ker (locRes₂S S X (extArithLoc S (Sum.inl ())))).map (locPi S X) ⊔ W = ⊤
  rw [eq_top_iff]
  rintro z -
  obtain ⟨x, c, hx, hzq⟩ := hz z
  have hz' : (z : LocProd S X) = locPi S X x + ∑ i, c i • w' i := by
    funext q
    rw [hzq q]
    change _ = locRes₂S S X (extArithLoc S (Sum.inr q)) x + projq S X q (∑ i, c i • w' i)
    congr 1
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul]
    rfl
  rw [hz']
  refine Submodule.add_mem_sup ⟨x, hx, rfl⟩ (Submodule.sum_mem _ fun i _ => ?_)
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end Supplement

end P2M5b7Odd
p2m_reactivate "P2MW.S_groupCohomology_exists_range_locRes_continuousH2S_sup_eq_top_finrank_le_finrank_invariants_dualTwist_of_ne_two.P2M5b7Odd"

end
p2m_reactivate "P2MW.S_groupCohomology_exists_range_locRes_continuousH2S_sup_eq_top_finrank_le_finrank_invariants_dualTwist_of_ne_two.P2M5b7Odd"

theorem solution
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hp2 : p ≠ 2) (hpS : pPrime p ∈ S)
    (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    [FiniteDimensional (ZMod p) M]
    (hsm : ∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s ∈ F.fixingSubgroup, M.ρ s m = m)
    (hMur : ∀ q : Nat.Primes, q ∉ S → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
      A.LiesOverPrime (q : ℕ) → ∀ g ∈ A.inertiaSubgroupIn ℚ, M.ρ g = 1)
    (hinf2 : Subsingleton (continuousH2 (extArithLoc S (Sum.inl ())) (Rep.res (extArithLoc S (Sum.inl ())) M))) :
    ∃ W : Submodule (ZMod p)
        (∀ q : ↥S, continuousH2 (extArithLoc S (Sum.inr q)) (Rep.res (extArithLoc S (Sum.inr q)) M)),
      Module.Finite (ZMod p) W ∧
      Module.finrank (ZMod p) W ≤ Module.finrank (ZMod p) (M.dualTwist (cycloChar p)).ρ.invariants ∧
      LinearMap.range (LinearMap.pi fun q : ↥S => locRes₂S S M (extArithLoc S (Sum.inr q))) ⊔ W = ⊤ := by
  classical

  obtain ⟨F, hFgal, hFS, hFM, hFζ, hF4⟩ := P2M5b7Odd.exists_galois_SLevel S hpS M hsm hMur
  haveI := hFgal
  haveI : FiniteDimensional ℚ F := hFS.1
  haveI hUn : F.fixingSubgroup.Normal := by
    simpa only [Subgroup.comap_id] using
      groupCohomology.normal_comap_fixingSubgroup (MonoidHom.id (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) F
  haveI hUf : F.fixingSubgroup.FiniteIndex := by
    simpa only [Subgroup.comap_id] using
      groupCohomology.finiteIndex_comap_fixingSubgroup (MonoidHom.id (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) F

  have hN : ∀ u : ↥F.fixingSubgroup, (Rep.res F.fixingSubgroup.subtype M).ρ u = 1 := fun u => hFM u u.2
  haveI : FiniteDimensional (ZMod p) (Rep.res F.fixingSubgroup.subtype M) := ‹FiniteDimensional (ZMod p) M›
  haveI := P2M5b7Odd.finiteDimensional_M₁ F.fixingSubgroup M

  obtain ⟨n, w, hn, hz⟩ := exists_forall_locRes_continuousH2S_coind_eq_add_sum_of_exists_sq_eq_neg_one S hpS F hFS
    hF4 hFζ (Rep.res F.fixingSubgroup.subtype M) hN
  have h₁ := P2M5b7Odd.exists_submodule_supplement S (P2M5b7Odd.M₁ F.fixingSubgroup M) n w hn hz

  obtain ⟨W, hWfin, hWle, hWsup⟩ := exists_range_locRes_continuousH2S_sup_eq_top_of_surjective_of_ne_two S hp2 hpS
    (P2M5b7Odd.M₁ F.fixingSubgroup M) M (P2M5b7Odd.hsm_M₁ F.fixingSubgroup M hFM F rfl)
    (P2M5b7Odd.eps F.fixingSubgroup M) (P2M5b7Odd.eps_equivariant F.fixingSubgroup M)
    (P2M5b7Odd.eps_surjective F.fixingSubgroup M hFM) h₁
  refine ⟨W, hWfin, hWle, ?_⟩
  rw [eq_top_iff, ← hWsup]
  exact sup_le_sup_right (LinearMap.map_le_range) W

end S_groupCohomology_exists_range_locRes_continuousH2S_sup_eq_top_finrank_le_finrank_invariants_dualTwist_of_ne_two
end P2MW
export P2MW.S_groupCohomology_exists_range_locRes_continuousH2S_sup_eq_top_finrank_le_finrank_invariants_dualTwist_of_ne_two (solution)
