-- Prove2me | solution 1 for groupCohomology.finprod_natCard_torsionBy_continuousH2_le_mul_natCard_torsionBy_continuousH2Sr_galoisSUnitsRep_of_sq_eq_neg_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/4506d4a4-4b5e-5cc2-92d5-3e2577da98f2

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousH2Map
import Definitions.Def_GroupCohomology_GaloisSUnits
import Definitions.Def_GroupCohomology_LevelSubgroup
import Theorems.Thm_groupCohomology_natCard_torsionBy_continuousH2_inf_map_conj_range_primeLocalToGlobal_le
import Theorems.Thm_groupCohomology_finite_continuousH2_inf_map_conj_range_archimedeanLoc_and_natCard_le_two
import Theorems.Thm_groupCohomology_pow_natCard_places_le_mul_natCard_torsionBy_continuousH2Sr_galoisSUnitsRep_of_sq_eq_neg_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_finprod_natCard_torsionBy_continuousH2_le_mul_natCard_torsionBy_continuousH2Sr_galoisSUnitsRep_of_sq_eq_neg_one
p2m_attr_erase "instance" "groupCohomology.Kummer.instMulDistribMulActionRootsOfUnity ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal NumberField.LevelArith.instCommGroupUnitsModPow M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup AlgebraicClosure.Rat.isGalois FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap NumberField.AdelicHaar.locallyCompactSpace_adeleRing NumberField.AdelicHaar.finite_residueField_adicCompletionIntegers NumberField.AdelicHaar.locallyCompactSpace_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_finiteAdeleRing NumberField.AdelicHaar.compactSpace_adicCompletionIntegers NumberField.AdelicHaar.t2Space_finiteAdeleRing NumberField.AdelicHaar.t2Space_matrix_adeleRing NumberField.AdelicHaar.t2Space_adeleRing NumberField.AdelicHaar.fact_isOpen_adicCompletionIntegers NumberField.AdelicHaar.t2Space_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_matrix_adeleRing NumberField.AdelicHaar.t2Space_infiniteAdeleRing NumberField.AdelicHaar.properSpace_adicCompletion"
p2m_attr_erase "instance" "M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite Deep.NTSupply.instNormalRayClassSubgroup instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal"
p2m_attr_erase "simp" "groupCohomology.Kummer.coe_kummerCocycleRoots groupCohomology.Kummer.mem_powerSubgroup_iff groupCohomology.Kummer.val_smul_units groupCohomology.Kummer.kummerHom_apply groupCohomology.Kummer.coe_smul_rootsOfUnity groupCohomology.unitsInflate₁_apply groupCohomology.unitsInflate₂_apply ExtCitation.LocalLevel.coe_smul_OO WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply IsLocalRing.principalUnits_zero groupCohomology.coe_continuousH1SrMap_apply groupCohomology.continuousH2SrMap_continuousH2Srπ groupCohomology.coe_levelCocyclesSr₂Map NumberField.LevelArith.coe_levelFieldEquiv NumberField.LevelArith.modP_apply_mk NumberField.LevelArith.coe_levelFieldEquiv_symm NumberField.LevelArith.torsionP_apply_coe NumberField.LevelArith.repTorsionPMap_hom_apply_coe NumberField.LevelArith.toZMod_apply NumberField.LevelArith.repModPMap_hom_mk NumberField.SUnits.val_zsmul NumberField.SUnits.val_add NumberField.LevelArith.smul_mk NumberField.LevelArith.selmerRepInt_ρ_apply NumberField.LevelArith.selmerRepField_ρ_apply NumberField.LevelArith.unitsModPowMap_mk M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk M4aHerbrand.IdeleGaloisDescent.classAct_mk M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq groupCohomology.continuousH2Inflation_H2π groupCohomology.levelInflate₂_apply groupCohomology.coe_levelInflateCocycles₂"
p2m_attr_erase "simp" "groupCohomology.levelInflate₁_apply M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq"
p2m_attr_erase "simp" "SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply"
p2m_attr_erase "simp" "AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply M4aHerbrand.Bridge.finiteConorm_apply M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec"
p2m_attr_erase "simp" "LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open CategoryTheory Module groupCohomology ExtCitation

noncomputable section

namespace P2MBcountH4

lemma finprod_finprod_le {A B : Type} [Fintype A] [Fintype B] {κ : A ⊕ B → Type} [∀ i, Finite (κ i)]
    (c : ∀ i, κ i → ℕ) (e p : ℕ)
    (hA : ∀ a j, c (Sum.inl a) j ≤ e) (hB : ∀ b j, c (Sum.inr b) j ≤ p) :
    ∏ᶠ i, ∏ᶠ j, c i j ≤ e ^ (∑ a, Nat.card (κ (Sum.inl a))) * p ^ (∑ b, Nat.card (κ (Sum.inr b))) := by
  classical
  letI : ∀ i, Fintype (κ i) := fun i => Fintype.ofFinite _
  have hi : ∀ i (b : ℕ), (∀ j, c i j ≤ b) → ∏ᶠ j, c i j ≤ b ^ Nat.card (κ i) := fun i b hb => by
    rw [finprod_eq_prod_of_fintype, Nat.card_eq_fintype_card, ← Finset.card_univ, ← Finset.prod_const]
    exact Finset.prod_le_prod (fun j _ => Nat.zero_le _) (fun j _ => hb j)
  rw [finprod_eq_prod_of_fintype, Fintype.prod_sum_type]
  refine Nat.mul_le_mul ?_ ?_
  · rw [← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun a _ => hi _ e (hA a))
  · rw [← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun b _ => hi _ p (hB b))

lemma mem_torsionBy_iff_zsmul {M : Type*} [AddCommGroup M] [Module ℤ M] (n : ℤ) (x : M) :
    x ∈ Submodule.torsionBy ℤ M n ↔ n • x = 0 := by
  rw [Submodule.mem_torsionBy_iff, ← Int.cast_smul_eq_zsmul ℤ n x, Int.cast_id]

lemma nsmul_eq_zero_of_mem_torsionBy {Y : Type} [AddCommGroup Y] {mY : Module ℤ Y} (p : ℕ) {y : Y}
    (hy : y ∈ Submodule.torsionBy ℤ Y (p : ℤ)) : p • y = 0 := by
  have h := (mem_torsionBy_iff_zsmul (p : ℤ) y).1 hy
  rwa [natCast_zsmul] at h

lemma eq_zero_of_odd_prime_nsmul {Y : Type} [AddCommGroup Y] [Finite Y] (h2 : Nat.card Y ≤ 2)
    (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) {y : Y} (hy : p • y = 0) : y = 0 := by
  have hpos : 0 < Nat.card Y := Nat.card_pos
  have hcY : Nat.card Y • y = 0 := card_nsmul_eq_zero'
  rcases (show Nat.card Y = 1 ∨ Nat.card Y = 2 by omega) with h1 | h2'
  · haveI : Subsingleton Y := (Nat.card_eq_one_iff_unique.1 h1).1
    exact Subsingleton.elim _ _
  · rw [h2'] at hcY
    obtain ⟨k, hk⟩ : ∃ k, p = 2 * k + 1 := (hp.out.eq_two_or_odd').resolve_left hp2
    rw [hk, add_nsmul, one_nsmul, mul_nsmul, hcY, nsmul_zero, zero_add] at hy
    exact hy

lemma torsionBy_bound (p : ℕ) [Fact p.Prime] {Y : Type} [AddCommGroup Y] {mY : Module ℤ Y}
    (hfin : Finite Y) (h2 : Nat.card Y ≤ 2) :
    Finite ↥(Submodule.torsionBy ℤ Y (p : ℤ)) ∧ Nat.card ↥(Submodule.torsionBy ℤ Y (p : ℤ)) ≤ 2 ∧
    (p ≠ 2 → Nat.card ↥(Submodule.torsionBy ℤ Y (p : ℤ)) ≤ 1) ∧
    (Subsingleton Y → Nat.card ↥(Submodule.torsionBy ℤ Y (p : ℤ)) ≤ 1) := by
  haveI := hfin
  refine ⟨inferInstance, (Finite.card_subtype_le _).trans h2, fun hp2 => ?_, fun hs => ?_⟩
  · refine Finite.card_le_one_iff_subsingleton.2 ⟨fun y₁ y₂ => Subtype.ext ?_⟩
    rw [eq_zero_of_odd_prime_nsmul h2 p hp2 (nsmul_eq_zero_of_mem_torsionBy p y₁.2),
      eq_zero_of_odd_prime_nsmul h2 p hp2 (nsmul_eq_zero_of_mem_torsionBy p y₂.2)]
  · exact Finite.card_le_one_iff_subsingleton.2 ⟨fun y₁ y₂ => Subtype.ext (Subsingleton.elim _ _)⟩

local notation "Γ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
local notation "ℚb" => (AlgebraicClosure ℚ)

variable (S : Finset Nat.Primes) (F : IntermediateField ℚ ℚb)

lemma finite_T (hF : F.IsUnramifiedOutside S) [IsGalois ℚ F] (v : extArithIndex S) :
    Finite (Γ ⧸ (F.fixingSubgroup ⊔ (extArithLoc S v).range)) := by
  haveI := hF.1
  haveI : (F.fixingSubgroup).FiniteIndex := by
    have := groupCohomology.finiteIndex_comap_fixingSubgroup (MonoidHom.id Γ) F
    rwa [Subgroup.comap_id] at this
  haveI : (F.fixingSubgroup ⊔ (extArithLoc S v).range).FiniteIndex := Subgroup.finiteIndex_of_le le_sup_left
  exact Subgroup.finite_quotient_of_finiteIndex

lemma conj_mem_iff [IsGalois ℚ F] (γ x : Γ) : γ * x * γ⁻¹ ∈ F.fixingSubgroup ↔ x ∈ F.fixingSubgroup := by
  haveI : (F.fixingSubgroup).Normal := by
    have := groupCohomology.normal_comap_fixingSubgroup (MonoidHom.id Γ) F
    rwa [Subgroup.comap_id] at this
  refine ⟨fun h => ?_, fun h => Subgroup.Normal.conj_mem inferInstance x h γ⟩
  have := Subgroup.Normal.conj_mem inferInstance _ h γ⁻¹
  simpa [mul_assoc] using this

end P2MBcountH4

end

set_option maxHeartbeats 3200000 in
open P2MBcountH4 in
theorem solution
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [IsGalois ℚ F] (hF : F.IsUnramifiedOutside S)
    (h4 : p = 2 → ∃ i ∈ F, i ^ 2 = -1)
    (γ : ∀ v : extArithIndex S, (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ (F.fixingSubgroup ⊔ (extArithLoc S v).range) →
      (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (hγ : ∀ v t, (γ v t : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ (F.fixingSubgroup ⊔ (extArithLoc S v).range)) = t) :
    Finite ↥(Submodule.torsionBy ℤ
        (continuousH2Sr F.fixingSubgroup.subtype S (Rep.res F.fixingSubgroup.subtype (galoisSUnitsRep S))) (p : ℤ)) ∧
    (∀ (v : extArithIndex S) (t : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ (F.fixingSubgroup ⊔ (extArithLoc S v).range)),
      Finite ↥(Submodule.torsionBy ℤ
        (continuousH2 (F.fixingSubgroup ⊓ ((extArithLoc S v).range.map (MulAut.conj (γ v t)).toMonoidHom)).subtype
          (Rep.res (F.fixingSubgroup ⊓ ((extArithLoc S v).range.map (MulAut.conj (γ v t)).toMonoidHom)).subtype
            (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)))) (p : ℤ))) ∧
    ∏ᶠ (v : extArithIndex S) (t : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ (F.fixingSubgroup ⊔ (extArithLoc S v).range)),
        Nat.card ↥(Submodule.torsionBy ℤ
          (continuousH2 (F.fixingSubgroup ⊓ ((extArithLoc S v).range.map (MulAut.conj (γ v t)).toMonoidHom)).subtype
            (Rep.res (F.fixingSubgroup ⊓ ((extArithLoc S v).range.map (MulAut.conj (γ v t)).toMonoidHom)).subtype
              (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)))) (p : ℤ))
      ≤ p * Nat.card ↥(Submodule.torsionBy ℤ
          (continuousH2Sr F.fixingSubgroup.subtype S (Rep.res F.fixingSubgroup.subtype (galoisSUnitsRep S))) (p : ℤ)) := by
  haveI := hF.1
  haveI hT : ∀ v : extArithIndex S,
      Finite ((AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ (F.fixingSubgroup ⊔ (extArithLoc S v).range)) := finite_T S F hF

  have hG :=
    groupCohomology.pow_natCard_places_le_mul_natCard_torsionBy_continuousH2Sr_galoisSUnitsRep_of_sq_eq_neg_one (p := p) S hpS F hF h4

  have hfin : ∀ (q : ↥S) (t : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ (F.fixingSubgroup ⊔ (extArithLoc S (Sum.inr q)).range)),
      Finite ↥(Submodule.torsionBy ℤ
        (continuousH2 (F.fixingSubgroup ⊓ ((extArithLoc S (Sum.inr q)).range.map (MulAut.conj (γ (Sum.inr q) t)).toMonoidHom)).subtype
          (Rep.res (F.fixingSubgroup ⊓ ((extArithLoc S (Sum.inr q)).range.map (MulAut.conj (γ (Sum.inr q) t)).toMonoidHom)).subtype
            (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)))) (p : ℤ)) ∧
      Nat.card ↥(Submodule.torsionBy ℤ
        (continuousH2 (F.fixingSubgroup ⊓ ((extArithLoc S (Sum.inr q)).range.map (MulAut.conj (γ (Sum.inr q) t)).toMonoidHom)).subtype
          (Rep.res (F.fixingSubgroup ⊓ ((extArithLoc S (Sum.inr q)).range.map (MulAut.conj (γ (Sum.inr q) t)).toMonoidHom)).subtype
            (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)))) (p : ℤ)) ≤ p :=
    fun q t => groupCohomology.natCard_torsionBy_continuousH2_inf_map_conj_range_primeLocalToGlobal_le p q.1 F (γ (Sum.inr q) t)

  have harch : ∀ (u : Unit) (t : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ (F.fixingSubgroup ⊔ (extArithLoc S (Sum.inl u)).range)),
      Finite ↥(Submodule.torsionBy ℤ
        (continuousH2 (F.fixingSubgroup ⊓ ((extArithLoc S (Sum.inl u)).range.map (MulAut.conj (γ (Sum.inl u) t)).toMonoidHom)).subtype
          (Rep.res (F.fixingSubgroup ⊓ ((extArithLoc S (Sum.inl u)).range.map (MulAut.conj (γ (Sum.inl u) t)).toMonoidHom)).subtype
            (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)))) (p : ℤ)) ∧
      Nat.card ↥(Submodule.torsionBy ℤ
        (continuousH2 (F.fixingSubgroup ⊓ ((extArithLoc S (Sum.inl u)).range.map (MulAut.conj (γ (Sum.inl u) t)).toMonoidHom)).subtype
          (Rep.res (F.fixingSubgroup ⊓ ((extArithLoc S (Sum.inl u)).range.map (MulAut.conj (γ (Sum.inl u) t)).toMonoidHom)).subtype
            (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)))) (p : ℤ)) ≤ 2 ∧
      (p ≠ 2 → Nat.card ↥(Submodule.torsionBy ℤ
        (continuousH2 (F.fixingSubgroup ⊓ ((extArithLoc S (Sum.inl u)).range.map (MulAut.conj (γ (Sum.inl u) t)).toMonoidHom)).subtype
          (Rep.res (F.fixingSubgroup ⊓ ((extArithLoc S (Sum.inl u)).range.map (MulAut.conj (γ (Sum.inl u) t)).toMonoidHom)).subtype
            (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)))) (p : ℤ)) ≤ 1) ∧
      (complexConjugation ∉ F.fixingSubgroup → Nat.card ↥(Submodule.torsionBy ℤ
        (continuousH2 (F.fixingSubgroup ⊓ ((extArithLoc S (Sum.inl u)).range.map (MulAut.conj (γ (Sum.inl u) t)).toMonoidHom)).subtype
          (Rep.res (F.fixingSubgroup ⊓ ((extArithLoc S (Sum.inl u)).range.map (MulAut.conj (γ (Sum.inl u) t)).toMonoidHom)).subtype
            (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)))) (p : ℤ)) ≤ 1) := by
    intro u t
    have hY :=
      groupCohomology.finite_continuousH2_inf_map_conj_range_archimedeanLoc_and_natCard_le_two F.fixingSubgroup (γ (Sum.inl u) t)
    have hb := torsionBy_bound p (mY := inferInstance) hY.1 hY.2.1
    exact ⟨hb.1, hb.2.1, hb.2.2.1, fun hc => hb.2.2.2 (hY.2.2 fun h => hc ((conj_mem_iff F _ _).1 h))⟩
  refine ⟨hG.1, fun v => match v with
    | Sum.inl u => fun t => (harch u t).1
    | Sum.inr q => fun t => (hfin q t).1, ?_⟩
  by_cases hcase : p = 2 ∧ complexConjugation ∈ F.fixingSubgroup
  ·
    calc _ ≤ 2 ^ (∑ a : Unit, Nat.card ((AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ (F.fixingSubgroup ⊔ (extArithLoc S (Sum.inl a)).range))) *
          p ^ (∑ q : ↥S, Nat.card ((AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ (F.fixingSubgroup ⊔ (extArithLoc S (Sum.inr q)).range))) :=
          finprod_finprod_le (A := Unit) (B := ↥S)
            (κ := fun v => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ (F.fixingSubgroup ⊔ (extArithLoc S v).range))
            (fun v t => Nat.card ↥(Submodule.torsionBy ℤ
              (continuousH2 (F.fixingSubgroup ⊓ ((extArithLoc S v).range.map (MulAut.conj (γ v t)).toMonoidHom)).subtype
                (Rep.res (F.fixingSubgroup ⊓ ((extArithLoc S v).range.map (MulAut.conj (γ v t)).toMonoidHom)).subtype
                  (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)))) (p : ℤ)))
            2 p (fun a j => (harch a j).2.1) (fun b j => (hfin b j).2)
      _ = p ^ ((∑ q : ↥S, Nat.card ((AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ (F.fixingSubgroup ⊔ (extArithLoc S (Sum.inr q)).range))) +
            Nat.card ((AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ (F.fixingSubgroup ⊔ (extArithLoc S (Sum.inl ())).range))) := by
          rw [hcase.1, Fintype.sum_unique, pow_add, mul_comm]
      _ ≤ _ := hG.2.2 hcase.1 hcase.2
  ·
    have hone : ∀ (u : Unit) (t : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ (F.fixingSubgroup ⊔ (extArithLoc S (Sum.inl u)).range)),
        Nat.card ↥(Submodule.torsionBy ℤ
          (continuousH2 (F.fixingSubgroup ⊓ ((extArithLoc S (Sum.inl u)).range.map (MulAut.conj (γ (Sum.inl u) t)).toMonoidHom)).subtype
            (Rep.res (F.fixingSubgroup ⊓ ((extArithLoc S (Sum.inl u)).range.map (MulAut.conj (γ (Sum.inl u) t)).toMonoidHom)).subtype
              (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)))) (p : ℤ)) ≤ 1 := by
      intro u t
      by_cases hp2 : p = 2
      · exact (harch u t).2.2.2 fun hc => hcase ⟨hp2, hc⟩
      · exact (harch u t).2.2.1 hp2
    calc _ ≤ 1 ^ (∑ a : Unit, Nat.card ((AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ (F.fixingSubgroup ⊔ (extArithLoc S (Sum.inl a)).range))) *
          p ^ (∑ q : ↥S, Nat.card ((AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ (F.fixingSubgroup ⊔ (extArithLoc S (Sum.inr q)).range))) :=
          finprod_finprod_le (A := Unit) (B := ↥S)
            (κ := fun v => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ (F.fixingSubgroup ⊔ (extArithLoc S v).range))
            (fun v t => Nat.card ↥(Submodule.torsionBy ℤ
              (continuousH2 (F.fixingSubgroup ⊓ ((extArithLoc S v).range.map (MulAut.conj (γ v t)).toMonoidHom)).subtype
                (Rep.res (F.fixingSubgroup ⊓ ((extArithLoc S v).range.map (MulAut.conj (γ v t)).toMonoidHom)).subtype
                  (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)))) (p : ℤ)))
            1 p hone (fun b j => (hfin b j).2)
      _ = p ^ (∑ q : ↥S, Nat.card ((AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ (F.fixingSubgroup ⊔ (extArithLoc S (Sum.inr q)).range))) := by
          rw [one_pow, one_mul]
      _ ≤ _ := hG.2.1

end S_groupCohomology_finprod_natCard_torsionBy_continuousH2_le_mul_natCard_torsionBy_continuousH2Sr_galoisSUnitsRep_of_sq_eq_neg_one
end P2MW
export P2MW.S_groupCohomology_finprod_natCard_torsionBy_continuousH2_le_mul_natCard_torsionBy_continuousH2Sr_galoisSUnitsRep_of_sq_eq_neg_one (solution)
