-- Prove2me | solution 1 for groupCohomology.exists_forall_eq_res_continuousH2Sr_trivial_add_smul_of_exists_sq_eq_neg_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/b0ac7da8-14dd-5441-9bc0-f79b2d511a02

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Definitions.Def_GroupCohomology_ContinuousH2Map
import Definitions.Def_GroupCohomology_LevelSubgroup
import Definitions.Def_GroupCohomology_GaloisSUnits
import Theorems.Thm_IntermediateField_IsUnramifiedOutside_normalClosure
import Theorems.Thm_groupCohomology_continuousH2Map_res_injective_of_isUnit_index
import Theorems.Thm_IntermediateField_IsUnramifiedOutside_sup_adjoin_simple_of_pow_mem
import Theorems.Thm_groupCohomology_exists_levelCocyclesSr2_sub_pow_mem_levelCoboundariesSr2_of_zsmul_mem
import Theorems.Thm_groupCohomology_mem_levelCoboundaries2_of_pow_mem_and_exists_pow_sub_mem_of_zsmul_mem
import Theorems.Thm_groupCohomology_exists_mem_levelCocyclesSr2_res_sub_mem_levelCoboundariesSr2_of_isUnit_index
import Theorems.Thm_groupCohomology_exists_forall_eq_res_continuousH2Sr_galoisSUnitsRep_add_zsmul_of_sq_eq_neg_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_exists_forall_eq_res_continuousH2Sr_trivial_add_smul_of_exists_sq_eq_neg_one
p2m_attr_erase "instance" "NumberField.LevelArith.instCommGroupUnitsModPow AlgebraicClosure.Rat.isGalois IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed"
p2m_attr_erase "instance" "RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion NumberField.AdelicHaar.locallyCompactSpace_adeleRing NumberField.AdelicHaar.finite_residueField_adicCompletionIntegers NumberField.AdelicHaar.locallyCompactSpace_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_finiteAdeleRing NumberField.AdelicHaar.compactSpace_adicCompletionIntegers NumberField.AdelicHaar.t2Space_finiteAdeleRing NumberField.AdelicHaar.t2Space_matrix_adeleRing NumberField.AdelicHaar.t2Space_adeleRing NumberField.AdelicHaar.fact_isOpen_adicCompletionIntegers NumberField.AdelicHaar.t2Space_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_matrix_adeleRing NumberField.AdelicHaar.t2Space_infiniteAdeleRing NumberField.AdelicHaar.properSpace_adicCompletion M4aHerbrand.Bridge.instT2SpaceAdeleRing M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite Deep.NTSupply.instNormalRayClassSubgroup instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal"
p2m_attr_erase "instance" "ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal groupCohomology.Kummer.instMulDistribMulActionRootsOfUnity LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal"
p2m_attr_erase "simp" "NumberField.LevelArith.coe_levelFieldEquiv NumberField.LevelArith.modP_apply_mk NumberField.LevelArith.coe_levelFieldEquiv_symm NumberField.LevelArith.torsionP_apply_coe NumberField.LevelArith.repTorsionPMap_hom_apply_coe NumberField.LevelArith.toZMod_apply NumberField.LevelArith.repModPMap_hom_mk NumberField.SUnits.val_zsmul NumberField.SUnits.val_add NumberField.LevelArith.smul_mk NumberField.LevelArith.selmerRepInt_ρ_apply NumberField.LevelArith.selmerRepField_ρ_apply NumberField.LevelArith.unitsModPowMap_mk NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq groupCohomology.continuousH2Inflation_H2π groupCohomology.levelInflate₂_apply groupCohomology.coe_levelInflateCocycles₂ groupCohomology.levelInflate₁_apply SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul"
p2m_attr_erase "simp" "IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply"
p2m_attr_erase "simp" "FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq M4aHerbrand.Bridge.finiteConorm_apply M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply"
p2m_attr_erase "simp" "Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk M4aHerbrand.IdeleGaloisDescent.classAct_mk Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent IsLocalRing.principalUnits_zero ExtCitation.LocalLevel.coe_smul_OO WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply groupCohomology.Kummer.coe_kummerCocycleRoots groupCohomology.Kummer.mem_powerSubgroup_iff groupCohomology.Kummer.val_smul_units groupCohomology.Kummer.kummerHom_apply"
p2m_attr_erase "simp" "groupCohomology.Kummer.coe_smul_rootsOfUnity groupCohomology.unitsInflate₁_apply groupCohomology.unitsInflate₂_apply AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option linter.unusedSectionVars false

open CategoryTheory Module groupCohomology ExtCitation

noncomputable section
namespace P2MW1cG

local notation "Γ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
local notation "ℚb" => (AlgebraicClosure ℚ)

local instance isAlgebraicQbar_w1c : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
local instance isAlgClosureQbar_w1c : IsAlgClosure ℚ (AlgebraicClosure ℚ) := ⟨inferInstance, inferInstance⟩
local instance normalQbar_w1c : Normal ℚ (AlgebraicClosure ℚ) := IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)

section Zeta

variable (p : ℕ) [hp : Fact p.Prime]

lemma exists_prim : ∃ ζ : ℚbˣ, IsPrimitiveRoot ζ p := by
  haveI : NeZero (p : ℚb) := NeZero.charZero
  have hdeg : (Polynomial.cyclotomic p ℚb).degree ≠ 0 := by
    rw [Polynomial.degree_cyclotomic]
    exact_mod_cast (Nat.totient_pos.2 hp.out.pos).ne'
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root _ hdeg
  have hprim : IsPrimitiveRoot x p := (Polynomial.isRoot_cyclotomic_iff).1 hx
  have hx0 : x ≠ 0 := hprim.ne_zero hp.out.ne_zero
  exact ⟨Units.mk0 x hx0, IsPrimitiveRoot.coe_units_iff.1 (by simpa using hprim)⟩

def zeta : ℚbˣ := (exists_prim p).choose

lemma zeta_spec : IsPrimitiveRoot (zeta p) p := (exists_prim p).choose_spec

lemma zeta_val_spec : IsPrimitiveRoot ((zeta p : ℚbˣ) : ℚb) p := (zeta_spec p).map_of_injective Units.coeHom_injective

lemma zeta_mem_galoisSUnits (S : Finset Nat.Primes) : zeta p ∈ galoisSUnits S := by
  intro A _
  have hpow : ((zeta p : ℚbˣ) : ℚb) ^ p = 1 := by
    rw [← Units.val_pow_eq_pow_val, (zeta_spec p).pow_eq_one, Units.val_one]
  have hv : A.valuation ((zeta p : ℚbˣ) : ℚb) = 1 := by
    have h1 : A.valuation ((zeta p : ℚbˣ) : ℚb) ^ p = 1 := by rw [← map_pow, hpow, map_one]
    rcases lt_trichotomy (A.valuation ((zeta p : ℚbˣ) : ℚb)) 1 with h | h | h
    · exact absurd h1 (pow_lt_one₀ zero_le' h hp.out.ne_zero).ne
    · exact h
    · exact absurd h1 (one_lt_pow₀ h hp.out.ne_zero).ne'
  refine ⟨(A.valuation_le_one_iff _).1 hv.le, (A.valuation_le_one_iff _).1 ?_⟩
  rw [Units.val_inv_eq_inv_val, map_inv₀, hv, inv_one]

variable (F : IntermediateField ℚ ℚb)

def Fz : IntermediateField ℚ ℚb := F ⊔ IntermediateField.adjoin ℚ {((zeta p : ℚbˣ) : ℚb)}

lemma le_Fz : F ≤ Fz p F := le_sup_left

lemma zeta_mem_Fz : ((zeta p : ℚbˣ) : ℚb) ∈ Fz p F :=
  (le_sup_right : IntermediateField.adjoin ℚ {((zeta p : ℚbˣ) : ℚb)} ≤ Fz p F) (IntermediateField.mem_adjoin_simple_self ℚ _)

lemma smul_zeta_of_mem {σ : Γ} (hσ : σ ∈ (Fz p F).fixingSubgroup) : σ • zeta p = zeta p := by
  ext
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ _ (zeta_mem_Fz p F)

scoped instance isGalois_adjoin_zeta : IsGalois ℚ (IntermediateField.adjoin ℚ {((zeta p : ℚbˣ) : ℚb)}) := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have hc := (zeta_val_spec p).intermediateField_adjoin_isCyclotomicExtension ℚ
  have := @IsCyclotomicExtension.isGalois {p} ℚ _ _ _ _ hc
  convert this <;> first | rfl | exact Subsingleton.elim _ _

scoped instance isAlgebraic_intermediateField (X : IntermediateField ℚ ℚb) : Algebra.IsAlgebraic ℚ X := by
  constructor
  intro x
  have := (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (x : ℚb))
  rw [← IntermediateField.isAlgebraic_iff] at this
  convert this <;> first | rfl | exact Subsingleton.elim _ _

scoped instance normal_Fz [IsGalois ℚ F] : Normal ℚ (Fz p F) := by
  have h1 : Normal ℚ F := inferInstance
  have h2 : Normal ℚ (IntermediateField.adjoin ℚ {((zeta p : ℚbˣ) : ℚb)}) := inferInstance
  have := @IntermediateField.normal_sup ℚ ℚb _ _ _ F (IntermediateField.adjoin ℚ {((zeta p : ℚbˣ) : ℚb)})
    (by convert h1 <;> first | rfl | exact Subsingleton.elim _ _) (by convert h2 <;> first | rfl | exact Subsingleton.elim _ _)
  unfold Fz; convert this <;> first | rfl | exact Subsingleton.elim _ _

scoped instance isGalois_Fz [IsGalois ℚ F] : IsGalois ℚ (Fz p F) := IsGalois.mk

lemma finiteDimensional_adjoin_zeta : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {((zeta p : ℚbˣ) : ℚb)}) := by
  have := IntermediateField.adjoin.finiteDimensional
    ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) ((zeta p : ℚbˣ) : ℚb)).isIntegral)
  convert this

scoped instance finiteDimensional_Fz [FiniteDimensional ℚ F] : FiniteDimensional ℚ (Fz p F) := by
  have := @IntermediateField.finiteDimensional_sup ℚ ℚb _ _ _ F (IntermediateField.adjoin ℚ {((zeta p : ℚbˣ) : ℚb)})
    (by convert (inferInstance : FiniteDimensional ℚ F)) (by convert finiteDimensional_adjoin_zeta p)
  unfold Fz; convert this

lemma isUnramifiedOutside_Fz (S : Finset Nat.Primes) (hpS : pPrime p ∈ S) (hF : F.IsUnramifiedOutside S) :
    (Fz p F).IsUnramifiedOutside S := by
  refine hF.sup_adjoin_simple_of_pow_mem S hp.out hpS (α := ((zeta p : ℚbˣ) : ℚb)) ?_ ?_
  · rw [← Units.val_pow_eq_pow_val, (zeta_spec p).pow_eq_one, Units.val_one]; exact one_mem _
  · intro A _
    rw [← Units.val_pow_eq_pow_val, (zeta_spec p).pow_eq_one, Units.val_one, inv_one]
    exact ⟨one_mem _, one_mem _⟩

end Zeta

lemma exists_normal_levelS (S : Finset Nat.Primes) {F' : IntermediateField ℚ ℚb} (hF' : F'.IsUnramifiedOutside S) :
    ∃ F'' : IntermediateField ℚ ℚb, F''.IsUnramifiedOutside S ∧ F''.fixingSubgroup.Normal ∧
      F''.fixingSubgroup ≤ F'.fixingSubgroup := by
  haveI := hF'.1
  haveI : Normal ℚ (IntermediateField.normalClosure ℚ F' ℚb) := by
    have := normalClosure.normal ℚ (↥F') ℚb; convert this <;> first | rfl | exact Subsingleton.elim _ _
  refine ⟨IntermediateField.normalClosure ℚ F' ℚb, hF'.normalClosure, ?_,
    IntermediateField.fixingSubgroup_antitone (IntermediateField.le_normalClosure F')⟩
  have := groupCohomology.normal_comap_fixingSubgroup (MonoidHom.id Γ) (IntermediateField.normalClosure ℚ F' ℚb)
  rwa [Subgroup.comap_id] at this

lemma exists_normal_level (F' : IntermediateField ℚ ℚb) [FiniteDimensional ℚ F'] :
    ∃ F'' : IntermediateField ℚ ℚb, FiniteDimensional ℚ F'' ∧ F''.fixingSubgroup.Normal ∧
      F''.fixingSubgroup ≤ F'.fixingSubgroup := by
  haveI : Normal ℚ (IntermediateField.normalClosure ℚ F' ℚb) := by
    have := normalClosure.normal ℚ (↥F') ℚb; convert this <;> first | rfl | exact Subsingleton.elim _ _
  refine ⟨IntermediateField.normalClosure ℚ F' ℚb, inferInstance, ?_,
    IntermediateField.fixingSubgroup_antitone (IntermediateField.le_normalClosure F')⟩
  have := groupCohomology.normal_comap_fixingSubgroup (MonoidHom.id Γ) (IntermediateField.normalClosure ℚ F' ℚb)
  rwa [Subgroup.comap_id] at this

section ConjPull

variable (k : Type) [CommRing k]

abbrev Tr (A : Subgroup Γ) : Rep k ↥A := Rep.trivial k ↥A k

def IsConj {A B : Subgroup Γ} (ψ : ↥A →* ↥B) : Prop := ∃ g : Γ, ∀ a : ↥A, (ψ a : Γ) = g⁻¹ * a * g

variable {A B C : Subgroup Γ}

variable {k} in

lemma conj_cocycle_sub_triv {G : Type} [Group G] (x : G × G → k) (hx : x ∈ cocycles₂ (Rep.trivial k G k)) (γ a b : G) :
    x (γ * a * γ⁻¹, γ * b * γ⁻¹) - x (a, b) =
      ((x (γ⁻¹, γ * b * γ⁻¹) - x (b, γ⁻¹)) - (x (γ⁻¹, γ * (a * b) * γ⁻¹) - x (a * b, γ⁻¹))
        + (x (γ⁻¹, γ * a * γ⁻¹) - x (a, γ⁻¹))) := by
  rw [mem_cocycles₂_iff] at hx
  have h1 := hx a b γ⁻¹
  have h2 := hx a γ⁻¹ (γ * b * γ⁻¹)
  have h3 := hx γ⁻¹ (γ * a * γ⁻¹) (γ * b * γ⁻¹)
  simp only [Representation.trivial_apply] at h1 h2 h3
  have e2 : γ⁻¹ * (γ * b * γ⁻¹) = b * γ⁻¹ := by group
  have e3 : γ⁻¹ * (γ * a * γ⁻¹) = a * γ⁻¹ := by group
  have e3' : γ * a * γ⁻¹ * (γ * b * γ⁻¹) = γ * (a * b) * γ⁻¹ := by group
  rw [e2] at h2
  rw [e3, e3'] at h3
  linear_combination h2 - h1 - h3

section finiteFamily

variable (ψ : ↥A →* ↥B) (hψ : IsConj ψ)
include hψ

omit [CommRing k] in
lemma isLevelConstant₂_precomp {X : Type} {y : ↥B × ↥B → X} (hy : IsLevelConstant₂ B.subtype y) :
    IsLevelConstant₂ A.subtype (y ∘ Prod.map ψ ψ) := by
  obtain ⟨g, hg⟩ := hψ
  obtain ⟨F', hF', hc⟩ := hy
  haveI := hF'
  obtain ⟨F'', hF'', hN, hle⟩ := exists_normal_level F'
  refine ⟨F'', hF'', fun a a' s s' hs hs' => ?_⟩
  simp only [Function.comp_apply, Prod.map_apply, map_mul]
  apply hc
  · rw [Subgroup.coe_subtype, hg]; exact hle (hN.conj_mem' _ hs g)
  · rw [Subgroup.coe_subtype, hg]; exact hle (hN.conj_mem' _ hs' g)

omit [CommRing k] in
lemma isLevelConstant₁_precomp {X : Type} {y : ↥B → X} (hy : IsLevelConstant₁ B.subtype y) :
    IsLevelConstant₁ A.subtype (y ∘ ψ) := by
  obtain ⟨g, hg⟩ := hψ
  obtain ⟨F', hF', hc⟩ := hy
  haveI := hF'
  obtain ⟨F'', hF'', hN, hle⟩ := exists_normal_level F'
  refine ⟨F'', hF'', fun a s hs => ?_⟩
  simp only [Function.comp_apply, map_mul]
  apply hc
  rw [Subgroup.coe_subtype, hg]; exact hle (hN.conj_mem' _ hs g)

lemma pull_mem_levelCocycles₂ {y : ↥B × ↥B → k} (hy : y ∈ levelCocycles₂ B.subtype (Tr k B)) :
    cochainsPullPush₂ (A := Tr k B) (B := Tr k A) ψ LinearMap.id y ∈ levelCocycles₂ A.subtype (Tr k A) :=
  ⟨cochainsPullPush₂_mem_cocycles₂ (A := Tr k B) (B := Tr k A) ψ LinearMap.id (fun _ _ => rfl) hy.1,
    isLevelConstant₂_precomp ψ hψ hy.2⟩

lemma pull_mem_levelCoboundaries₂ {y : ↥B × ↥B → k} (hy : y ∈ levelCoboundaries₂ B.subtype (Tr k B)) :
    cochainsPullPush₂ (A := Tr k B) (B := Tr k A) ψ LinearMap.id y ∈ levelCoboundaries₂ A.subtype (Tr k A) := by
  obtain ⟨e, he, rfl⟩ := (mem_levelCoboundaries₂_iff _ _ _).1 hy
  refine (mem_levelCoboundaries₂_iff _ _ _).2 ⟨cochainsPullPush₁ (A := Tr k B) (B := Tr k A) ψ LinearMap.id e,
    isLevelConstant₁_precomp ψ hψ he, ?_⟩
  exact (cochainsPullPush₂_d₁₂ (A := Tr k B) (B := Tr k A) ψ LinearMap.id (fun _ _ => rfl) e).symm

def conjPull : continuousH2 B.subtype (Tr k B) →ₗ[k] continuousH2 A.subtype (Tr k A) :=
  Submodule.mapQ _ _ ((cochainsPullPush₂ (A := Tr k B) (B := Tr k A) ψ LinearMap.id).restrict
    fun _ hy => pull_mem_levelCocycles₂ k ψ hψ hy) fun _ hy => pull_mem_levelCoboundaries₂ k ψ hψ hy

lemma conjPull_mk (y : ↥(levelCocycles₂ B.subtype (Tr k B))) :
    conjPull k ψ hψ (continuousH2π _ _ y) =
      continuousH2π _ _ ⟨cochainsPullPush₂ (A := Tr k B) (B := Tr k A) ψ LinearMap.id y, pull_mem_levelCocycles₂ k ψ hψ y.2⟩ :=
  rfl

end finiteFamily

omit [CommRing k] in
lemma IsConj.comp' {ψ : ↥A →* ↥B} {ψ' : ↥B →* ↥C} (h' : IsConj ψ') (h : IsConj ψ) : IsConj (ψ'.comp ψ) := by
  obtain ⟨g, hg⟩ := h
  obtain ⟨g', hg'⟩ := h'
  refine ⟨g * g', fun a => ?_⟩
  rw [MonoidHom.comp_apply, hg', hg]; group

omit [CommRing k] in
lemma IsConj.comp {ψ : ↥A →* ↥B} {ψ' : ↥B →* ↥C} (h : IsConj ψ) (h' : IsConj ψ') : IsConj (ψ'.comp ψ) := by
  obtain ⟨g, hg⟩ := h
  obtain ⟨g', hg'⟩ := h'
  refine ⟨g * g', fun a => ?_⟩
  rw [MonoidHom.comp_apply, hg', hg]; group

lemma conjPull_conjPull (ψ : ↥A →* ↥B) (hψ : IsConj ψ) (ψ' : ↥B →* ↥C) (hψ' : IsConj ψ') (h'' : IsConj (ψ'.comp ψ))
    (x : continuousH2 C.subtype (Tr k C)) :
    conjPull k ψ hψ (conjPull k ψ' hψ' x) = conjPull k (ψ'.comp ψ) h'' x := by
  obtain ⟨y, rfl⟩ := continuousH2π_surjective_aux x
  rfl
where
  continuousH2π_surjective_aux (x : continuousH2 C.subtype (Tr k C)) : ∃ y, continuousH2π _ _ y = x :=
    Submodule.mkQ_surjective _ x

lemma conjPull_congr (ψ ψ' : ↥A →* ↥B) (hψ : IsConj ψ) (hψ' : IsConj ψ') (h : ∀ a, ψ a = ψ' a)
    (x : continuousH2 B.subtype (Tr k B)) : conjPull k ψ hψ x = conjPull k ψ' hψ' x := by
  obtain rfl : ψ = ψ' := MonoidHom.ext h
  rfl

lemma conjPull_id (h : IsConj (MonoidHom.id ↥A)) (x : continuousH2 A.subtype (Tr k A)) : conjPull k (MonoidHom.id ↥A) h x = x := by
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ x
  rfl

lemma conjPull_inner (b : ↥A) (ψ : ↥A →* ↥A) (hψb : ∀ a, ψ a = b⁻¹ * a * b) (hψ : IsConj ψ)
    (x : continuousH2 A.subtype (Tr k A)) : conjPull k ψ hψ x = x := by
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ x
  change continuousH2π _ _ _ = continuousH2π _ _ _
  rw [← sub_eq_zero, ← map_sub, continuousH2π_eq_zero_iff]

  set γ : ↥A := b⁻¹ with hγ
  refine (mem_levelCoboundaries₂_iff _ _ _).2 ⟨fun a => (y : ↥A × ↥A → k) (γ⁻¹, γ * a * γ⁻¹) - (y : ↥A × ↥A → k) (a, γ⁻¹), ?_, ?_⟩
  ·
    obtain ⟨F', hF', hc⟩ := y.2.2
    haveI := hF'
    obtain ⟨F'', hF'', hN, hle⟩ := exists_normal_level F'
    refine ⟨F'', hF'', fun a s hs => ?_⟩
    have hs' : A.subtype s ∈ F'.fixingSubgroup := hle hs
    have hcs : A.subtype (γ * s * γ⁻¹) ∈ F'.fixingSubgroup := by
      simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv]
      exact hle (hN.conj_mem _ hs _)
    have e1 : γ * (a * s) * γ⁻¹ = γ * a * γ⁻¹ * (γ * s * γ⁻¹) := by group
    simp only
    rw [e1]
    have := hc (γ⁻¹ * 1) (γ * a * γ⁻¹) 1 (γ * s * γ⁻¹) (by simp) hcs
    rw [mul_one, mul_one] at this
    rw [this]
    have := hc a γ⁻¹ s 1 hs' (by simp)
    rw [mul_one] at this
    rw [this]
  · ext ⟨a, a'⟩
    rw [d₁₂_hom_apply]
    simp only [Representation.trivial_apply, Submodule.coe_sub, Pi.sub_apply]
    change _ = (y : ↥A × ↥A → k) (ψ a, ψ a') - (y : ↥A × ↥A → k) (a, a')
    have ha : ψ a = γ * a * γ⁻¹ := by rw [hψb, hγ, inv_inv]
    have ha' : ψ a' = γ * a' * γ⁻¹ := by rw [hψb, hγ, inv_inv]
    rw [ha, ha', conj_cocycle_sub_triv (y : ↥A × ↥A → k) y.2.1 γ a a']

section SFamily

variable (S : Finset Nat.Primes) (ψ : ↥A →* ↥B) (hψ : IsConj ψ)
include hψ

omit [CommRing k] in
lemma isLevelConstantSr₂_precomp {X : Type} {y : ↥B × ↥B → X} (hy : IsLevelConstantSr₂ B.subtype S y) :
    IsLevelConstantSr₂ A.subtype S (y ∘ Prod.map ψ ψ) := by
  obtain ⟨g, hg⟩ := hψ
  obtain ⟨F', hF', hc⟩ := hy
  obtain ⟨F'', hF'', hN, hle⟩ := exists_normal_levelS S hF'
  refine ⟨F'', hF'', fun a a' s s' hs hs' => ?_⟩
  simp only [Function.comp_apply, Prod.map_apply, map_mul]
  apply hc
  · rw [Subgroup.coe_subtype, hg]; exact hle (hN.conj_mem' _ hs g)
  · rw [Subgroup.coe_subtype, hg]; exact hle (hN.conj_mem' _ hs' g)

omit [CommRing k] in
lemma isLevelConstantSr₁_precomp {X : Type} {y : ↥B → X} (hy : IsLevelConstantSr₁ B.subtype S y) :
    IsLevelConstantSr₁ A.subtype S (y ∘ ψ) := by
  obtain ⟨g, hg⟩ := hψ
  obtain ⟨F', hF', hc⟩ := hy
  obtain ⟨F'', hF'', hN, hle⟩ := exists_normal_levelS S hF'
  refine ⟨F'', hF'', fun a s hs => ?_⟩
  simp only [Function.comp_apply, map_mul]
  apply hc
  rw [Subgroup.coe_subtype, hg]; exact hle (hN.conj_mem' _ hs g)

lemma pullS_mem_levelCocyclesSr₂ {y : ↥B × ↥B → k} (hy : y ∈ levelCocyclesSr₂ B.subtype S (Tr k B)) :
    cochainsPullPush₂ (A := Tr k B) (B := Tr k A) ψ LinearMap.id y ∈ levelCocyclesSr₂ A.subtype S (Tr k A) :=
  ⟨cochainsPullPush₂_mem_cocycles₂ (A := Tr k B) (B := Tr k A) ψ LinearMap.id (fun _ _ => rfl) hy.1,
    isLevelConstantSr₂_precomp S ψ hψ hy.2⟩

lemma pullS_mem_levelCoboundariesSr₂ {y : ↥B × ↥B → k} (hy : y ∈ levelCoboundariesSr₂ B.subtype S (Tr k B)) :
    cochainsPullPush₂ (A := Tr k B) (B := Tr k A) ψ LinearMap.id y ∈ levelCoboundariesSr₂ A.subtype S (Tr k A) := by
  obtain ⟨e, he, rfl⟩ := (mem_levelCoboundariesSr₂_iff _ _ _ _).1 hy
  refine (mem_levelCoboundariesSr₂_iff _ _ _ _).2 ⟨cochainsPullPush₁ (A := Tr k B) (B := Tr k A) ψ LinearMap.id e,
    isLevelConstantSr₁_precomp S ψ hψ he, ?_⟩
  exact (cochainsPullPush₂_d₁₂ (A := Tr k B) (B := Tr k A) ψ LinearMap.id (fun _ _ => rfl) e).symm

lemma pullM_mem_levelCocycles₂ {y : ↥B × ↥B → k} (hy : y ∈ levelCocyclesSr₂ B.subtype S (Tr k B)) :
    cochainsPullPush₂ (A := Tr k B) (B := Tr k A) ψ LinearMap.id y ∈ levelCocycles₂ A.subtype (Tr k A) :=
  levelCocyclesSr₂_le_levelCocycles₂ _ _ _ (pullS_mem_levelCocyclesSr₂ k S ψ hψ hy)

lemma pullM_mem_levelCoboundaries₂ {y : ↥B × ↥B → k} (hy : y ∈ levelCoboundariesSr₂ B.subtype S (Tr k B)) :
    cochainsPullPush₂ (A := Tr k B) (B := Tr k A) ψ LinearMap.id y ∈ levelCoboundaries₂ A.subtype (Tr k A) :=
  levelCoboundariesSr₂_le_levelCoboundaries₂ _ _ _ (pullS_mem_levelCoboundariesSr₂ k S ψ hψ hy)

def conjPullS : continuousH2Sr B.subtype S (Tr k B) →ₗ[k] continuousH2Sr A.subtype S (Tr k A) :=
  Submodule.mapQ _ _ ((cochainsPullPush₂ (A := Tr k B) (B := Tr k A) ψ LinearMap.id).restrict
    fun _ hy => pullS_mem_levelCocyclesSr₂ k S ψ hψ hy) fun _ hy => pullS_mem_levelCoboundariesSr₂ k S ψ hψ hy

def mixPull : continuousH2Sr B.subtype S (Tr k B) →ₗ[k] continuousH2 A.subtype (Tr k A) :=
  Submodule.mapQ _ _ ((cochainsPullPush₂ (A := Tr k B) (B := Tr k A) ψ LinearMap.id).restrict
    fun _ hy => pullM_mem_levelCocycles₂ k S ψ hψ hy) fun _ hy => pullM_mem_levelCoboundaries₂ k S ψ hψ hy

lemma conjPullS_mk (y : ↥(levelCocyclesSr₂ B.subtype S (Tr k B))) :
    conjPullS k S ψ hψ (continuousH2Srπ _ _ _ y) =
      continuousH2Srπ _ _ _ ⟨cochainsPullPush₂ (A := Tr k B) (B := Tr k A) ψ LinearMap.id y, pullS_mem_levelCocyclesSr₂ k S ψ hψ y.2⟩ :=
  rfl

lemma mixPull_mk (y : ↥(levelCocyclesSr₂ B.subtype S (Tr k B))) :
    mixPull k S ψ hψ (continuousH2Srπ _ _ _ y) =
      continuousH2π _ _ ⟨cochainsPullPush₂ (A := Tr k B) (B := Tr k A) ψ LinearMap.id y, pullM_mem_levelCocycles₂ k S ψ hψ y.2⟩ :=
  rfl

end SFamily

variable (S : Finset Nat.Primes)

lemma conjPullS_conjPullS (ψ : ↥A →* ↥B) (hψ : IsConj ψ) (ψ' : ↥B →* ↥C) (hψ' : IsConj ψ') (h'' : IsConj (ψ'.comp ψ))
    (x : continuousH2Sr C.subtype S (Tr k C)) :
    conjPullS k S ψ hψ (conjPullS k S ψ' hψ' x) = conjPullS k S (ψ'.comp ψ) h'' x := by
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ x
  rfl

lemma mixPull_conjPullS (ψ : ↥A →* ↥B) (hψ : IsConj ψ) (ψ' : ↥B →* ↥C) (hψ' : IsConj ψ') (h'' : IsConj (ψ'.comp ψ))
    (x : continuousH2Sr C.subtype S (Tr k C)) :
    mixPull k S ψ hψ (conjPullS k S ψ' hψ' x) = mixPull k S (ψ'.comp ψ) h'' x := by
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ x
  rfl

lemma conjPull_mixPull (ψ : ↥A →* ↥B) (hψ : IsConj ψ) (ψ' : ↥B →* ↥C) (hψ' : IsConj ψ') (h'' : IsConj (ψ'.comp ψ))
    (x : continuousH2Sr C.subtype S (Tr k C)) :
    conjPull k ψ hψ (mixPull k S ψ' hψ' x) = mixPull k S (ψ'.comp ψ) h'' x := by
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ x
  rfl

lemma conjPullS_congr (ψ ψ' : ↥A →* ↥B) (hψ : IsConj ψ) (hψ' : IsConj ψ') (h : ∀ a, ψ a = ψ' a)
    (x : continuousH2Sr B.subtype S (Tr k B)) : conjPullS k S ψ hψ x = conjPullS k S ψ' hψ' x := by
  obtain rfl : ψ = ψ' := MonoidHom.ext h
  rfl

lemma mixPull_congr (ψ ψ' : ↥A →* ↥B) (hψ : IsConj ψ) (hψ' : IsConj ψ') (h : ∀ a, ψ a = ψ' a)
    (x : continuousH2Sr B.subtype S (Tr k B)) : mixPull k S ψ hψ x = mixPull k S ψ' hψ' x := by
  obtain rfl : ψ = ψ' := MonoidHom.ext h
  rfl

lemma conjPullS_inner (b : ↥A) (ψ : ↥A →* ↥A) (hψb : ∀ a, ψ a = b⁻¹ * a * b) (hψ : IsConj ψ)
    (x : continuousH2Sr A.subtype S (Tr k A)) : conjPullS k S ψ hψ x = x := by
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ x
  change continuousH2Srπ _ _ _ _ = continuousH2Srπ _ _ _ _
  rw [← sub_eq_zero, ← map_sub, continuousH2Srπ_eq_zero_iff]
  set γ : ↥A := b⁻¹ with hγ
  refine (mem_levelCoboundariesSr₂_iff _ _ _ _).2
    ⟨fun a => (y : ↥A × ↥A → k) (γ⁻¹, γ * a * γ⁻¹) - (y : ↥A × ↥A → k) (a, γ⁻¹), ?_, ?_⟩
  · obtain ⟨F', hF', hc⟩ := y.2.2
    obtain ⟨F'', hF'', hN, hle⟩ := exists_normal_levelS S hF'
    refine ⟨F'', hF'', fun a s hs => ?_⟩
    have hs' : A.subtype s ∈ F'.fixingSubgroup := hle hs
    have hcs : A.subtype (γ * s * γ⁻¹) ∈ F'.fixingSubgroup := by
      simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv]
      exact hle (hN.conj_mem _ hs _)
    have e1 : γ * (a * s) * γ⁻¹ = γ * a * γ⁻¹ * (γ * s * γ⁻¹) := by group
    simp only
    rw [e1]
    have := hc (γ⁻¹ * 1) (γ * a * γ⁻¹) 1 (γ * s * γ⁻¹) (by simp) hcs
    rw [mul_one, mul_one] at this
    rw [this]
    have := hc a γ⁻¹ s 1 hs' (by simp)
    rw [mul_one] at this
    rw [this]
  · ext ⟨a, a'⟩
    rw [d₁₂_hom_apply]
    simp only [Representation.trivial_apply, Submodule.coe_sub, Pi.sub_apply]
    change _ = (y : ↥A × ↥A → k) (ψ a, ψ a') - (y : ↥A × ↥A → k) (a, a')
    have ha : ψ a = γ * a * γ⁻¹ := by rw [hψb, hγ, inv_inv]
    have ha' : ψ a' = γ * a' * γ⁻¹ := by rw [hψb, hγ, inv_inv]
    rw [ha, ha', conj_cocycle_sub_triv (y : ↥A × ↥A → k) (levelCocyclesSr₂_le_cocycles₂ _ _ _ y.2) γ a a']

lemma loc_eq_mixPull (hle : A ≤ B) (h : IsConj (Subgroup.inclusion hle)) (x : continuousH2Sr B.subtype S (Tr k B)) :
    continuousH2Map (rH := B.subtype) (rG := A.subtype) (A := Tr k B) (B := Tr k A) (Subgroup.inclusion hle) (fun _ => rfl)
        LinearMap.id (fun _ _ => rfl) (continuousH2SrToContinuousH2 B.subtype S (Tr k B) x) =
      mixPull k S (Subgroup.inclusion hle) h x := by
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ x
  rfl

omit [CommRing k] in
lemma isConj_inclusion (hle : A ≤ B) : IsConj (Subgroup.inclusion hle) := ⟨1, fun a => by simp⟩

end ConjPull

section Expo

variable (p : ℕ) [hp : Fact p.Prime]

abbrev Un (A : Subgroup Γ) : Rep ℤ ↥A := Rep.res A.subtype (Rep.ofAlgebraAutOnUnits ℚ ℚb)

abbrev SUn (S : Finset Nat.Primes) (A : Subgroup Γ) : Rep ℤ ↥A := Rep.res A.subtype (galoisSUnitsRep S)

lemma zeta_pow_mod (m : ℕ) : (zeta p) ^ (m % p) = (zeta p) ^ m := by
  conv_rhs => rw [← Nat.mod_add_div m p, pow_add, pow_mul, (zeta_spec p).pow_eq_one, one_pow, mul_one]

def chi : ZMod p →+ Additive ℚbˣ :=
  AddMonoidHom.mk' (fun n => Additive.ofMul (zeta p ^ n.val)) fun a b => by
    change Additive.ofMul (zeta p ^ (a + b).val) = _
    rw [← ofMul_mul, ← pow_add, ZMod.val_add, zeta_pow_mod]

lemma chi_apply (n : ZMod p) : chi p n = Additive.ofMul (zeta p ^ n.val) := rfl

variable (S : Finset Nat.Primes)

def chiS : ZMod p →+ Additive ↥(galoisSUnits S) :=
  AddMonoidHom.mk' (fun n => Additive.ofMul ⟨zeta p ^ n.val, Subgroup.pow_mem _ (zeta_mem_galoisSUnits p S) _⟩) fun a b => by
    change Additive.ofMul (⟨zeta p ^ (a + b).val, _⟩ : ↥(galoisSUnits S)) = _
    rw [← ofMul_mul]
    congr 1
    apply Subtype.ext
    change zeta p ^ (a + b).val = zeta p ^ a.val * zeta p ^ b.val
    rw [← pow_add, ZMod.val_add, zeta_pow_mod]

lemma chiS_apply (n : ZMod p) :
    chiS p S n = Additive.ofMul ⟨zeta p ^ n.val, Subgroup.pow_mem _ (zeta_mem_galoisSUnits p S) _⟩ := rfl

variable {A : Subgroup Γ} (hA : ∀ σ ∈ A, σ • zeta p = zeta p)

def expo (z : ↥A × ↥A → ZMod p) : ↥A × ↥A → Un A := chi p ∘ z

def expoS (z : ↥A × ↥A → ZMod p) : ↥A × ↥A → SUn S A := chiS p S ∘ z

lemma expo_add (z z' : ↥A × ↥A → ZMod p) : expo p (z + z') = expo p z + expo p z' := by
  funext g; exact map_add (chi p) (z g) (z' g)

lemma expo_sub (z z' : ↥A × ↥A → ZMod p) : expo p (z - z') = expo p z - expo p z' := by
  funext g; exact map_sub (chi p) (z g) (z' g)

lemma expo_zsmul (c : ℤ) (z : ↥A × ↥A → ZMod p) : expo p (c • z) = c • expo p z := by
  funext g; exact map_zsmul (chi p) c (z g)

lemma expo_zero : expo p (0 : ↥A × ↥A → ZMod p) = 0 := by
  funext g; exact map_zero (chi p)

include hA

lemma ρ_chi (a : ↥A) (n : ZMod p) : (Un A).ρ a (chi p n) = chi p n := by
  change (Rep.ofMulDistribMulAction Γ ℚbˣ).ρ (a : Γ) (chi p n) = chi p n
  rw [chi_apply, Rep.ofMulDistribMulAction_ρ_apply_apply, toMul_ofMul, smul_pow', hA _ a.2]

lemma ρ_chiS (a : ↥A) (n : ZMod p) : (SUn S A).ρ a (chiS p S n) = chiS p S n := by
  change (Rep.ofMulDistribMulAction Γ ↥(galoisSUnits S)).ρ (a : Γ) (chiS p S n) = chiS p S n
  rw [chiS_apply, Rep.ofMulDistribMulAction_ρ_apply_apply, toMul_ofMul]
  congr 1
  apply Subtype.ext
  rw [coe_smul_galoisSUnits, smul_pow', hA _ a.2]

lemma expo_mem_levelCocycles₂ {z : ↥A × ↥A → ZMod p} (hz : z ∈ levelCocycles₂ A.subtype (Tr (ZMod p) A)) :
    expo p z ∈ levelCocycles₂ A.subtype (Un A) := by
  refine ⟨(?_ : expo p z ∈ cocycles₂ (Un A)), hz.2.comp _⟩
  rw [mem_cocycles₂_iff]
  intro g h j
  have := (mem_cocycles₂_iff _).1 hz.1 g h j
  simp only [Representation.trivial_apply] at this
  simp only [expo, Function.comp_apply]
  rw [ρ_chi p hA]
  have h2 := congrArg (chi p) this
  rw [map_add, map_add] at h2
  exact h2

lemma expo_mem_levelCoboundaries₂ {z : ↥A × ↥A → ZMod p} (hz : z ∈ levelCoboundaries₂ A.subtype (Tr (ZMod p) A)) :
    expo p z ∈ levelCoboundaries₂ A.subtype (Un A) := by
  obtain ⟨w, hw, rfl⟩ := (mem_levelCoboundaries₂_iff _ _ _).1 hz
  refine (mem_levelCoboundaries₂_iff _ _ _).2 ⟨chi p ∘ w, hw.comp _, ?_⟩
  funext ⟨g, h⟩
  simp only [expo, Function.comp_apply, d₁₂_hom_apply, Rep.trivial_ρ_apply, Representation.trivial_apply]
  rw [ρ_chi p hA]
  have h2 := (map_sub (chi p) (w h) (w (g * h)))
  have h3 := map_add (chi p) (w h - w (g * h)) (w g)
  rw [h2] at h3
  exact h3.symm

lemma expoS_mem_levelCocyclesSr₂ {z : ↥A × ↥A → ZMod p} (hz : z ∈ levelCocyclesSr₂ A.subtype S (Tr (ZMod p) A)) :
    expoS p S z ∈ levelCocyclesSr₂ A.subtype S (SUn S A) := by
  refine ⟨(?_ : expoS p S z ∈ cocycles₂ (SUn S A)), hz.2.comp _⟩
  rw [mem_cocycles₂_iff]
  intro g h j
  have := (mem_cocycles₂_iff _).1 hz.1 g h j
  simp only [Representation.trivial_apply] at this
  simp only [expoS, Function.comp_apply]
  rw [ρ_chiS p S hA]
  have h2 := congrArg (chiS p S) this
  rw [map_add, map_add] at h2
  exact h2

omit hA in

lemma p_zsmul_eq_zero {X : Type} (Y : X → ZMod p) : (p : ℤ) • Y = 0 := by
  funext g; simp

end Expo

lemma πS_eq_iff {k G : Type} [CommRing k] [Group G] (r : G →* Γ) (S : Finset Nat.Primes) (M : Rep k G)
    (a b : ↥(levelCocyclesSr₂ r S M)) :
    continuousH2Srπ r S M a = continuousH2Srπ r S M b ↔ (a : G × G → M) - b ∈ levelCoboundariesSr₂ r S M :=
  (Submodule.Quotient.eq _).trans Iff.rfl

lemma π_eq_iff {k G : Type} [CommRing k] [Group G] (r : G →* Γ) (M : Rep k G) (a b : ↥(levelCocycles₂ r M)) :
    continuousH2π r M a = continuousH2π r M b ↔ (a : G × G → M) - b ∈ levelCoboundaries₂ r M :=
  (Submodule.Quotient.eq _).trans Iff.rfl

section OverZeta

variable (p : ℕ) [hp : Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
  (E : IntermediateField ℚ ℚb) [IsGalois ℚ E] (hES : E.IsUnramifiedOutside S)
  (hEζ : ∀ σ ∈ E.fixingSubgroup, σ • zeta p = zeta p)
  (γE : ∀ q : ↥S, Γ ⧸ (E.fixingSubgroup ⊔ (extArithLoc S (Sum.inr q)).range) → Γ)
  (hγE : ∀ q t, (γE q t : Γ ⧸ (E.fixingSubgroup ⊔ (extArithLoc S (Sum.inr q)).range)) = t)

set_option hygiene false in
local notation "UE" => IntermediateField.fixingSubgroup E

abbrev DD (U : Subgroup Γ) (q : ↥S) (g : Γ) : Subgroup Γ := U ⊓ ((extArithLoc S (Sum.inr q)).range.map (MulAut.conj g).toMonoidHom)

lemma DD_le (U : Subgroup Γ) (q : ↥S) (g : Γ) : DD S U q g ≤ U := inf_le_left

include hpS hES hEζ hγE in

theorem core_zeta (hE4 : p = 2 → ∃ i ∈ E, i ^ 2 = -1) :
    ∃ w' : ∀ (q : ↥S) (t : Γ ⧸ (E.fixingSubgroup ⊔ (extArithLoc S (Sum.inr q)).range)),
        continuousH2 (DD S E.fixingSubgroup q (γE q t)).subtype (Tr (ZMod p) (DD S E.fixingSubgroup q (γE q t))),
      ∀ y' : ∀ (q : ↥S) (t : Γ ⧸ (E.fixingSubgroup ⊔ (extArithLoc S (Sum.inr q)).range)),
          continuousH2 (DD S E.fixingSubgroup q (γE q t)).subtype (Tr (ZMod p) (DD S E.fixingSubgroup q (γE q t))),
        ∃ (x' : continuousH2Sr E.fixingSubgroup.subtype S (Tr (ZMod p) E.fixingSubgroup)) (c : ZMod p),
          ∀ q t, y' q t = mixPull (ZMod p) S (Subgroup.inclusion (DD_le S E.fixingSubgroup q (γE q t)))
              (isConj_inclusion _) x' + c • w' q t := by
  classical

  obtain ⟨wE, hwEp, hcore⟩ :=
    groupCohomology.exists_forall_eq_res_continuousH2Sr_galoisSUnitsRep_add_zsmul_of_sq_eq_neg_one S hpS E hES hE4 γE hγE
  have hDζ : ∀ (q : ↥S) t, ∀ σ ∈ DD S UE q (γE q t), σ • zeta p = zeta p := fun q t σ hσ => hEζ σ hσ.1

  have hK := fun q t => groupCohomology.mem_levelCoboundaries2_of_pow_mem_and_exists_pow_sub_mem_of_zsmul_mem
    (p := p) (DD S UE q (γE q t)) (zeta p) (zeta_spec p) (hDζ q t)

  have hWex : ∀ q t, ∃ W : ↥(DD S UE q (γE q t)) × ↥(DD S UE q (γE q t)) → ZMod p,
      W ∈ levelCocycles₂ (DD S UE q (γE q t)).subtype (Tr (ZMod p) (DD S UE q (γE q t))) ∧
      ∃ WE : ↥(levelCocycles₂ (DD S UE q (γE q t)).subtype (Un (DD S UE q (γE q t)))),
        continuousH2π _ _ WE = wE q t ∧
        WE.1 - expo p W ∈ levelCoboundaries₂ (DD S UE q (γE q t)).subtype (Un (DD S UE q (γE q t))) := by
    intro q t
    obtain ⟨WE, hWE⟩ := Submodule.mkQ_surjective _ (wE q t)
    have hpWE : (p : ℤ) • WE.1 ∈ levelCoboundaries₂ (DD S UE q (γE q t)).subtype (Un (DD S UE q (γE q t))) := by
      have := hwEp q t
      rw [← hWE, ← map_zsmul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap] at this
      exact this
    obtain ⟨W, hW, hWW⟩ := (hK q t).2 WE.1 WE.2 hpWE
    exact ⟨W, hW, WE, hWE, hWW⟩
  choose W hW WE hWEw hWEW using hWex
  refine ⟨fun q t => continuousH2π _ _ ⟨W q t, hW q t⟩, fun y' => ?_⟩

  have hYex : ∀ q t, ∃ Y : ↥(levelCocycles₂ (DD S UE q (γE q t)).subtype (Tr (ZMod p) (DD S UE q (γE q t)))),
      continuousH2π _ _ Y = y' q t := fun q t => Submodule.mkQ_surjective _ (y' q t)
  choose Y hY using hYex

  obtain ⟨yE, hyE⟩ : ∃ yE : ∀ (q : ↥S) (t : Γ ⧸ (UE ⊔ (extArithLoc S (Sum.inr q)).range)),
      continuousH2 (DD S UE q (γE q t)).subtype (Un (DD S UE q (γE q t))),
      yE = fun q t => continuousH2π _ _ ⟨expo p (Y q t).1, expo_mem_levelCocycles₂ p (hDζ q t) (Y q t).2⟩ :=
    ⟨_, rfl⟩
  have hyEp : ∀ q t, (p : ℤ) • yE q t = 0 := by
    intro q t
    rw [hyE, ← map_zsmul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
    change (p : ℤ) • expo p (Y q t).1 ∈ _
    rw [← expo_zsmul, p_zsmul_eq_zero, expo_zero]
    exact zero_mem _
  obtain ⟨xE, c, hxEp, hxE⟩ := hcore yE hyEp
  subst hyE

  obtain ⟨XE, hXE⟩ := Submodule.mkQ_surjective _ xE
  subst hXE
  have hpXE : (p : ℤ) • XE.1 ∈ levelCoboundariesSr₂ (UE).subtype S (SUn S UE) := by
    have := hxEp
    rw [← map_zsmul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap] at this
    exact this
  obtain ⟨z, hz, hzX⟩ :=
    groupCohomology.exists_levelCocyclesSr2_sub_pow_mem_levelCoboundariesSr2_of_zsmul_mem S hpS UE
      ⟨E, hES, le_rfl⟩ (zeta p) (zeta_spec p) (zeta_mem_galoisSUnits p S) hEζ XE.1 XE.2 hpXE
  refine ⟨continuousH2Srπ _ _ _ ⟨z, hz⟩, (c : ZMod p), fun q t => ?_⟩

  have hzX' : XE.1 - expoS p S z ∈ levelCoboundariesSr₂ (UE).subtype S (SUn S UE) := hzX

  have h2 : cochainsPullPush₂ (A := SUn S UE) (B := Un (DD S UE q (γE q t)))
      (Subgroup.inclusion (DD_le S UE q (γE q t))) (galoisSUnitsToUnits S) (XE.1 - expoS p S z) ∈
      levelCoboundaries₂ (DD S UE q (γE q t)).subtype (Un (DD S UE q (γE q t))) :=
    levelCoboundariesSr₂_le_levelCoboundaries₂ _ _ _
      (cochainsPullPush₂_mem_levelCoboundariesSr₂ (rH := (UE).subtype) (rG := (DD S UE q (γE q t)).subtype)
        (A := SUn S UE) (B := Un (DD S UE q (γE q t)))
        (Subgroup.inclusion (DD_le S UE q (γE q t))) (fun _ => rfl) S (galoisSUnitsToUnits S) (fun _ _ => rfl) hzX')
  rw [map_sub] at h2

  have hzD : cochainsPullPush₂ (A := Tr (ZMod p) UE) (B := Tr (ZMod p) (DD S UE q (γE q t)))
      (Subgroup.inclusion (DD_le S UE q (γE q t))) LinearMap.id z ∈
      levelCocycles₂ (DD S UE q (γE q t)).subtype (Tr (ZMod p) (DD S UE q (γE q t))) :=
    pullM_mem_levelCocycles₂ (ZMod p) S _ (isConj_inclusion _) hz
  have hRz : cochainsPullPush₂ (A := SUn S UE) (B := Un (DD S UE q (γE q t)))
      (Subgroup.inclusion (DD_le S UE q (γE q t))) (galoisSUnitsToUnits S) (expoS p S z) =
      expo p (cochainsPullPush₂ (A := Tr (ZMod p) UE) (B := Tr (ZMod p) (DD S UE q (γE q t)))
        (Subgroup.inclusion (DD_le S UE q (γE q t))) LinearMap.id z) := rfl
  rw [hRz] at h2

  have e2 : continuousH2π _ _ (levelCocycles₂Map (rH := (UE).subtype) (rG := (DD S UE q (γE q t)).subtype)
        (A := SUn S UE) (B := Un (DD S UE q (γE q t)))
        (Subgroup.inclusion (DD_le S UE q (γE q t))) (fun _ => rfl) (galoisSUnitsToUnits S) (fun _ _ => rfl)
        (levelCocyclesSr₂ToLevelCocycles₂ _ S _ XE)) =
      continuousH2π ((DD S UE q (γE q t)).subtype) (Un (DD S UE q (γE q t)))
        ⟨_, expo_mem_levelCocycles₂ p (hDζ q t) hzD⟩ :=
    (π_eq_iff _ _ _ _).2 (by (first | exact h2 | simpa only [coe_levelCocycles₂Map] using h2 | (have h__ := h2; simp only [coe_levelCocycles₂Map] at h__; exact h__)))
  have e3 : wE q t = continuousH2π ((DD S UE q (γE q t)).subtype) (Un (DD S UE q (γE q t)))
      ⟨_, expo_mem_levelCocycles₂ p (hDζ q t) (hW q t)⟩ := (hWEw q t).symm.trans ((π_eq_iff _ _ _ _).2 (hWEW q t))
  have h1 : continuousH2π _ _ ⟨expo p (Y q t).1, expo_mem_levelCocycles₂ p (hDζ q t) (Y q t).2⟩ =
      continuousH2π ((DD S UE q (γE q t)).subtype) (Un (DD S UE q (γE q t))) ⟨_, expo_mem_levelCocycles₂ p (hDζ q t) hzD⟩ +
        c • continuousH2π ((DD S UE q (γE q t)).subtype) (Un (DD S UE q (γE q t)))
          ⟨_, expo_mem_levelCocycles₂ p (hDζ q t) (hW q t)⟩ :=
    (hxE q t).trans (congrArg₂ (· + ·) e2 (congrArg (fun v => c • v) e3))
  have e4 : continuousH2π ((DD S UE q (γE q t)).subtype) (Un (DD S UE q (γE q t))) ⟨_, expo_mem_levelCocycles₂ p (hDζ q t) hzD⟩ +
        c • continuousH2π ((DD S UE q (γE q t)).subtype) (Un (DD S UE q (γE q t)))
          ⟨_, expo_mem_levelCocycles₂ p (hDζ q t) (hW q t)⟩ =
      continuousH2π ((DD S UE q (γE q t)).subtype) (Un (DD S UE q (γE q t)))
        ⟨expo p _ + c • expo p (W q t), add_mem (expo_mem_levelCocycles₂ p (hDζ q t) hzD)
          (zsmul_mem (expo_mem_levelCocycles₂ p (hDζ q t) (hW q t)) c)⟩ := by
    rw [← map_zsmul, ← map_add]; rfl
  have h4 := (π_eq_iff _ _ _ _).1 (h1.trans e4)
  have h4' : expo p ((Y q t).1 - (cochainsPullPush₂ (A := Tr (ZMod p) UE) (B := Tr (ZMod p) (DD S UE q (γE q t)))
        (Subgroup.inclusion (DD_le S UE q (γE q t))) LinearMap.id z + c • W q t)) ∈
      levelCoboundaries₂ (DD S UE q (γE q t)).subtype (Un (DD S UE q (γE q t))) := by
    rw [expo_sub, expo_add, expo_zsmul]; exact h4

  have h5 := (hK q t).1 ((Y q t).1 - (cochainsPullPush₂ (A := Tr (ZMod p) UE) (B := Tr (ZMod p) (DD S UE q (γE q t)))
        (Subgroup.inclusion (DD_le S UE q (γE q t))) LinearMap.id z + c • W q t))
    (sub_mem (Y q t).2 (add_mem hzD (zsmul_mem (hW q t) c))) h4'

  refine (hY q t).symm.trans ?_
  have e6 : continuousH2π _ _ (Y q t) = continuousH2π ((DD S UE q (γE q t)).subtype) (Tr (ZMod p) (DD S UE q (γE q t)))
      ⟨_, add_mem hzD (zsmul_mem (hW q t) c)⟩ := (π_eq_iff _ _ _ _).2 h5
  refine e6.trans ?_
  have e7 : continuousH2π ((DD S UE q (γE q t)).subtype) (Tr (ZMod p) (DD S UE q (γE q t)))
        ⟨_, add_mem hzD (zsmul_mem (hW q t) c)⟩ =
      continuousH2π ((DD S UE q (γE q t)).subtype) (Tr (ZMod p) (DD S UE q (γE q t))) ⟨_, hzD⟩ +
        (c : ZMod p) • continuousH2π _ _ ⟨W q t, hW q t⟩ := by
    rw [Int.cast_smul_eq_zsmul, ← map_zsmul, ← map_add]; rfl
  exact e7

end OverZeta

section Descent

variable (p : ℕ) [hp : Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
  (F : IntermediateField ℚ ℚb) [IsGalois ℚ F] (hF : F.IsUnramifiedOutside S)

set_option hygiene false in
local notation "U" => IntermediateField.fixingSubgroup F
set_option hygiene false in
local notation "U'" => IntermediateField.fixingSubgroup (Fz p F)
set_option hygiene false in
local notation "ζ" => zeta p

lemma U'_le : U' ≤ U := IntermediateField.fixingSubgroup_antitone (le_Fz p F)

scoped instance normal_U : Subgroup.Normal U := by
  have := groupCohomology.normal_comap_fixingSubgroup (MonoidHom.id Γ) F
  rwa [Subgroup.comap_id] at this

scoped instance normal_U' : Subgroup.Normal U' := by
  have := groupCohomology.normal_comap_fixingSubgroup (MonoidHom.id Γ) (Fz p F)
  rwa [Subgroup.comap_id] at this

lemma mem_U'_iff {σ : Γ} (hσ : σ ∈ U) : σ ∈ U' ↔ σ • ζ = ζ := by
  constructor
  · exact smul_zeta_of_mem p F
  · intro h
    have h' : σ ((ζ : ℚbˣ) : ℚb) = ((ζ : ℚbˣ) : ℚb) := by
      have := congrArg (fun u : ℚbˣ => (u : ℚb)) h
      exact this
    change σ ∈ (Fz p F).fixingSubgroup
    rw [Fz, IntermediateField.fixingSubgroup_sup, Subgroup.mem_inf]
    refine ⟨hσ, ?_⟩
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have hle : IntermediateField.adjoin ℚ {((ζ : ℚbˣ) : ℚb)} ≤ IntermediateField.fixedField (Subgroup.zpowers σ) := by
      rw [IntermediateField.adjoin_simple_le_iff, IntermediateField.mem_fixedField_iff]
      intro f hf
      have hst : Subgroup.zpowers σ ≤ MulAction.stabilizer Γ ((ζ : ℚbˣ) : ℚb) := by
        rw [Subgroup.zpowers_le, MulAction.mem_stabilizer_iff]
        exact h'
      exact hst hf
    exact (IntermediateField.mem_fixedField_iff _ _).1 (hle hx) σ (Subgroup.mem_zpowers σ)

lemma isUnit_index_of_le (A : Subgroup Γ) (hA : A ≤ U) :
    ((U').subgroupOf A).FiniteIndex ∧ IsUnit ((((U').subgroupOf A).index : ℕ) : ZMod p) := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  haveI : Fact (1 < p) := ⟨hp.out.one_lt⟩
  let χ : ↥A →* (ZMod p)ˣ := ((zeta_val_spec p).autToPow ℚ).comp A.subtype
  have hker : χ.ker = (U').subgroupOf A := by
    ext a
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_U'_iff p F (hA a.2)]
    have hspec := (zeta_val_spec p).autToPow_spec ℚ (a : Γ)
    change ((zeta_val_spec p).autToPow ℚ (a : Γ)) = 1 ↔ _
    constructor
    · intro h1
      rw [h1, Units.val_one, ZMod.val_one, pow_one] at hspec
      ext; exact hspec.symm
    · intro h2
      have h2' : (a : Γ) ((ζ : ℚbˣ) : ℚb) = ((ζ : ℚbˣ) : ℚb) := by
        have := congrArg (fun u : ℚbˣ => (u : ℚb)) h2; exact this
      rw [h2'] at hspec
      have h3 : ((zeta_val_spec p).autToPow ℚ (a : Γ) : ZMod p).val = 1 := by
        apply (zeta_val_spec p).pow_inj (ZMod.val_lt _) hp.out.one_lt
        rw [hspec, pow_one]
      ext
      rw [Units.val_one]
      apply ZMod.val_injective p
      rw [h3, ZMod.val_one]
  have hidx : ((U').subgroupOf A).index = Nat.card χ.range := by rw [← hker, Subgroup.index_ker]
  have hdvd : ((U').subgroupOf A).index ∣ p - 1 := by
    rw [hidx]
    have := Subgroup.card_subgroup_dvd_card χ.range
    rwa [Nat.card_eq_fintype_card (α := (ZMod p)ˣ), ZMod.card_units_eq_totient, Nat.totient_prime hp.out] at this
  have hne : ((U').subgroupOf A).index ≠ 0 := by
    intro h0; rw [h0] at hdvd
    have := Nat.eq_zero_of_zero_dvd hdvd
    have := hp.out.one_lt; omega
  refine ⟨⟨hne⟩, ?_⟩
  rw [ZMod.isUnit_iff_coprime]
  refine ((Nat.Prime.coprime_iff_not_dvd hp.out).2 fun hpd => ?_).symm
  have h1 := Nat.le_of_dvd (by have := hp.out.one_lt; omega) (dvd_trans hpd hdvd)
  have := hp.out.one_lt
  omega

omit [IsGalois ℚ F] in
lemma map_conj_eq_self_of_mem (H : Subgroup Γ) {κ : Γ} (hκ : κ ∈ H) : H.map (MulAut.conj κ).toMonoidHom = H := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact H.mul_mem (H.mul_mem hκ hy) (H.inv_mem hκ)
  · intro hx
    exact ⟨κ⁻¹ * x * κ, H.mul_mem (H.mul_mem (H.inv_mem hκ) hx) hκ, by simp [MulAut.conj_apply, mul_assoc]⟩

omit [IsGalois ℚ F] in
lemma map_conj_eq_self_of_normal (N : Subgroup Γ) [hN : N.Normal] (g : Γ) : N.map (MulAut.conj g).toMonoidHom = N := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hN.conj_mem _ hy _
  · intro hx
    refine ⟨g⁻¹ * x * g, hN.conj_mem' _ hx _, by simp [MulAut.conj_apply, mul_assoc]⟩

omit [IsGalois ℚ F] in
lemma map_conj_mul (H : Subgroup Γ) (a b : Γ) :
    H.map (MulAut.conj (a * b)).toMonoidHom = (H.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1

omit [IsGalois ℚ F] in
lemma map_conj_inf (H H' : Subgroup Γ) (a : Γ) :
    (H ⊓ H').map (MulAut.conj a).toMonoidHom = H.map (MulAut.conj a).toMonoidHom ⊓ H'.map (MulAut.conj a).toMonoidHom :=
  Subgroup.map_inf H H' _ (MulAut.conj a).injective

variable (γ : ∀ q : ↥S, Γ ⧸ ((U) ⊔ (extArithLoc S (Sum.inr q)).range) → Γ)
  (hγ : ∀ q t, (γ q t : Γ ⧸ ((U) ⊔ (extArithLoc S (Sum.inr q)).range)) = t)

set_option hygiene false in
local notation "K[" q "]" => MonoidHom.range (extArithLoc S (Sum.inr q))
set_option hygiene false in
local notation "T[" q "]" => Γ ⧸ ((IntermediateField.fixingSubgroup F) ⊔ MonoidHom.range (extArithLoc S (Sum.inr q)))
set_option hygiene false in
local notation "T'[" q "]" => Γ ⧸ ((IntermediateField.fixingSubgroup (Fz p F)) ⊔ MonoidHom.range (extArithLoc S (Sum.inr q)))

def π (q : ↥S) : T'[q] → T[q] := Subgroup.quotientMapOfLE (sup_le_sup_right (U'_le p F) _)

lemma π_mk (q : ↥S) (g : Γ) : π p S F q (g : T'[q]) = (g : T[q]) := Subgroup.quotientMapOfLE_apply_mk _ g

lemma π_smul (q : ↥S) (u : ↥U) (t' : T'[q]) : π p S F q ((u : Γ) • t') = π p S F q t' := by
  induction t' using QuotientGroup.induction_on with
  | H g =>
    rw [MulAction.Quotient.smul_mk, π_mk, π_mk, smul_eq_mul]
    symm
    rw [QuotientGroup.eq]
    have : g⁻¹ * ((u : Γ) * g) = g⁻¹ * u * g⁻¹⁻¹ := by group
    rw [this]
    exact Subgroup.mem_sup_left ((normal_U F).conj_mem' _ u.2 _)

include hγ in
lemma exists_rep (q : ↥S) (t' : T'[q]) : ∃ u : ↥U, ((((u : Γ) * γ q (π p S F q t') : Γ)) : T'[q]) = t' := by
  induction t' using QuotientGroup.induction_on with
  | H g =>
    have h1 : (γ q (π p S F q (g : T'[q])) : T[q]) = (g : T[q]) := by rw [hγ, π_mk]
    rw [QuotientGroup.eq, ← SetLike.mem_coe, Subgroup.normal_mul] at h1
    obtain ⟨u, hu, k, hk, huk⟩ := Set.mem_mul.1 h1
    refine ⟨⟨γ q (π p S F q (g : T'[q])) * u * (γ q (π p S F q (g : T'[q])))⁻¹, (normal_U F).conj_mem _ hu _⟩, ?_⟩
    rw [QuotientGroup.eq]
    have : (γ q (π p S F q ↑g) * u * (γ q (π p S F q ↑g))⁻¹ * γ q (π p S F q ↑g))⁻¹ * g = k := by
      have e : k = u⁻¹ * ((γ q (π p S F q ↑g))⁻¹ * g) := by rw [← huk]; group
      rw [e]; group
    rw [this]
    exact Subgroup.mem_sup_right hk

def uu (q : ↥S) (t' : T'[q]) : ↥U := (exists_rep p S F γ hγ q t').choose

lemma uu_spec (q : ↥S) (t' : T'[q]) : ((((uu p S F γ hγ q t' : Γ) * γ q (π p S F q t') : Γ)) : T'[q]) = t' :=
  (exists_rep p S F γ hγ q t').choose_spec

def γ' (q : ↥S) (t' : T'[q]) : Γ := (uu p S F γ hγ q t' : Γ) * γ q (π p S F q t')

lemma hγ' (q : ↥S) (t' : T'[q]) : (γ' p S F γ hγ q t' : T'[q]) = t' := uu_spec p S F γ hγ q t'

abbrev D (q : ↥S) (t : T[q]) : Subgroup Γ := DD S U q (γ q t)
abbrev D' (q : ↥S) (t' : T'[q]) : Subgroup Γ := DD S U' q (γ' p S F γ hγ q t')

include hγ in

lemma exists_decomp (q : ↥S) (u : ↥U) (t' : T'[q]) :
    ∃ ω : Γ, ω ∈ U' ∧ ∃ κ : Γ, κ ∈ D S F γ q (π p S F q t') ∧
      ((uu p S F γ hγ q ((u : Γ) • t') : Γ))⁻¹ * u * uu p S F γ hγ q t' = ω * κ := by
  have hπ : π p S F q ((u : Γ) • t') = π p S F q t' := π_smul p S F q u t'
  have h1 : (γ' p S F γ hγ q ((u : Γ) • t') : T'[q]) = (((u : Γ) * γ' p S F γ hγ q t' : Γ) : T'[q]) := by
    rw [hγ', ← smul_eq_mul, ← MulAction.Quotient.smul_mk, hγ']
  rw [QuotientGroup.eq, ← SetLike.mem_coe, Subgroup.normal_mul] at h1
  obtain ⟨ω₀, hω₀, k, hk, hωk⟩ := Set.mem_mul.1 h1
  set γt := γ q (π p S F q t') with hγt
  have hrew : γ' p S F γ hγ q ((u : Γ) • t') = uu p S F γ hγ q ((u : Γ) • t') * γt := by
    rw [γ', hπ]
  rw [hrew] at hωk
  refine ⟨γt * ω₀ * γt⁻¹, (normal_U' p F).conj_mem _ hω₀ _, γt * k * γt⁻¹, ⟨?_, ?_⟩, ?_⟩
  ·
    have : γt * k * γt⁻¹ = (γt * ω₀ * γt⁻¹)⁻¹ *
        (((uu p S F γ hγ q ((u : Γ) • t') : Γ))⁻¹ * u * uu p S F γ hγ q t') := by
      have e : ω₀ * k = (uu p S F γ hγ q ((u : Γ) • t') * γt)⁻¹ * ((u : Γ) * γ' p S F γ hγ q t') := hωk
      rw [γ'] at e
      have : k = ω₀⁻¹ * (γt⁻¹ * ((uu p S F γ hγ q ((u : Γ) • t') : Γ))⁻¹ * (u * ((uu p S F γ hγ q t' : Γ) * γt))) := by
        rw [← inv_mul_eq_iff_eq_mul.mpr e]; group
      rw [this]; group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (U'_le p F ((normal_U' p F).conj_mem _ hω₀ _)))
      (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (uu p S F γ hγ q _).2) u.2) (uu p S F γ hγ q t').2)
  · exact ⟨k, hk, rfl⟩
  · have e : ω₀ * k = (uu p S F γ hγ q ((u : Γ) • t') * γt)⁻¹ * ((u : Γ) * γ' p S F γ hγ q t') := hωk
    rw [γ'] at e
    calc ((uu p S F γ hγ q ((u : Γ) • t') : Γ))⁻¹ * u * uu p S F γ hγ q t'
        = γt * ((uu p S F γ hγ q ((u : Γ) • t') * γt)⁻¹ * ((u : Γ) * ((uu p S F γ hγ q t' : Γ) * γt))) * γt⁻¹ := by group
      _ = γt * (ω₀ * k) * γt⁻¹ := by rw [e]
      _ = γt * ω₀ * γt⁻¹ * (γt * k * γt⁻¹) := by group

section Data

variable (q : ↥S) (u : ↥U) (t' : T'[q])

def ω : Γ := (exists_decomp p S F γ hγ q u t').choose
lemma ω_mem : ω p S F γ hγ q u t' ∈ U' := (exists_decomp p S F γ hγ q u t').choose_spec.1

def κ : Γ := (exists_decomp p S F γ hγ q u t').choose_spec.2.choose
lemma κ_mem : κ p S F γ hγ q u t' ∈ D S F γ q (π p S F q t') := (exists_decomp p S F γ hγ q u t').choose_spec.2.choose_spec.1
lemma decomp_eq : ((uu p S F γ hγ q ((u : Γ) • t') : Γ))⁻¹ * u * uu p S F γ hγ q t' =
    ω p S F γ hγ q u t' * κ p S F γ hγ q u t' := (exists_decomp p S F γ hγ q u t').choose_spec.2.choose_spec.2

def ω' : Γ := uu p S F γ hγ q ((u : Γ) • t') * ω p S F γ hγ q u t' * (uu p S F γ hγ q ((u : Γ) • t') : Γ)⁻¹
lemma ω'_mem : ω' p S F γ hγ q u t' ∈ U' := (normal_U' p F).conj_mem _ (ω_mem p S F γ hγ q u t') _
def gg : Γ := (ω' p S F γ hγ q u t')⁻¹ * u

lemma gg_mem : gg p S F γ hγ q u t' ∈ U :=
  Subgroup.mul_mem _ (Subgroup.inv_mem _ (U'_le p F (ω'_mem p S F γ hγ q u t'))) u.2

lemma gg_mul_uu : gg p S F γ hγ q u t' * uu p S F γ hγ q t' = uu p S F γ hγ q ((u : Γ) • t') * κ p S F γ hγ q u t' := by
  have e := decomp_eq p S F γ hγ q u t'
  have e' : (u : Γ) * uu p S F γ hγ q t' = uu p S F γ hγ q ((u : Γ) • t') * (ω p S F γ hγ q u t' * κ p S F γ hγ q u t') := by
    rw [← e]; group
  rw [gg, ω', mul_assoc, e']; group

lemma κ_mem_C : κ p S F γ hγ q u t' ∈ (K[q]).map (MulAut.conj (γ q (π p S F q t'))).toMonoidHom :=
  (κ_mem p S F γ hγ q u t').2

lemma map_conj_gg (t'' : T'[q]) (h : (u : Γ) • t' = t'') :
    (D' p S F γ hγ q t').map (MulAut.conj (gg p S F γ hγ q u t')).toMonoidHom = D' p S F γ hγ q t'' := by
  subst h
  have hπ : π p S F q ((u : Γ) • t') = π p S F q t' := π_smul p S F q u t'
  change (U' ⊓ (K[q]).map (MulAut.conj (γ' p S F γ hγ q t')).toMonoidHom).map _ =
    U' ⊓ (K[q]).map (MulAut.conj (γ' p S F γ hγ q ((u : Γ) • t'))).toMonoidHom
  rw [map_conj_inf, map_conj_eq_self_of_normal, γ', γ', hπ, ← map_conj_mul, ← mul_assoc, gg_mul_uu, mul_assoc,
    map_conj_mul, map_conj_mul _ (uu p S F γ hγ q ((u : Γ) • t') : Γ),
    map_conj_mul _ (κ p S F γ hγ q u t'), map_conj_eq_self_of_mem _ (κ_mem_C p S F γ hγ q u t')]

def φh (s : T[q]) (h : π p S F q t' = s) : ↥(D' p S F γ hγ q t') →* ↥(D S F γ q s) where
  toFun d := ⟨(uu p S F γ hγ q t' : Γ)⁻¹ * d * uu p S F γ hγ q t', by
    subst h
    refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (uu p S F γ hγ q t').2) (U'_le p F d.2.1))
      (uu p S F γ hγ q t').2, ?_⟩
    have hd := d.2.2
    change (d : Γ) ∈ (K[q]).map (MulAut.conj (γ' p S F γ hγ q t')).toMonoidHom at hd
    rw [γ', map_conj_mul] at hd
    obtain ⟨y, hy, hyd⟩ := hd
    have : (uu p S F γ hγ q t' : Γ)⁻¹ * d * uu p S F γ hγ q t' = y := by
      rw [← hyd]; simp [MulAut.conj_apply, mul_assoc]
    rw [this]; exact hy⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' a b := by apply Subtype.ext; simp only [Subgroup.coe_mul]; group

lemma coe_φh (s : T[q]) (h : π p S F q t' = s) (d : ↥(D' p S F γ hγ q t')) :
    (φh p S F γ hγ q t' s h d : Γ) = (uu p S F γ hγ q t' : Γ)⁻¹ * d * uu p S F γ hγ q t' := rfl

lemma isConj_φh (s : T[q]) (h : π p S F q t' = s) : IsConj (φh p S F γ hγ q t' s h) :=
  ⟨uu p S F γ hγ q t', fun _ => rfl⟩

def ψh (t'' : T'[q]) (h : (u : Γ) • t' = t'') : ↥(D' p S F γ hγ q t'') →* ↥(D' p S F γ hγ q t') where
  toFun d := ⟨(gg p S F γ hγ q u t')⁻¹ * d * gg p S F γ hγ q u t', by
    have hd : (d : Γ) ∈ (D' p S F γ hγ q t').map (MulAut.conj (gg p S F γ hγ q u t')).toMonoidHom := by
      rw [map_conj_gg p S F γ hγ q u t' t'' h]; exact d.2
    obtain ⟨y, hy, hyd⟩ := hd
    have : (gg p S F γ hγ q u t')⁻¹ * d * gg p S F γ hγ q u t' = y := by
      rw [← hyd]; simp [MulAut.conj_apply, mul_assoc]
    rw [this]; exact hy⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' a b := by apply Subtype.ext; simp only [Subgroup.coe_mul]; group

lemma coe_ψh (t'' : T'[q]) (h : (u : Γ) • t' = t'') (d : ↥(D' p S F γ hγ q t'')) :
    (ψh p S F γ hγ q u t' t'' h d : Γ) = (gg p S F γ hγ q u t')⁻¹ * d * gg p S F γ hγ q u t' := rfl

lemma isConj_ψh (t'' : T'[q]) (h : (u : Γ) • t' = t'') : IsConj (ψh p S F γ hγ q u t' t'' h) :=
  ⟨gg p S F γ hγ q u t', fun _ => rfl⟩

def κ' (s : T[q]) (h : π p S F q t' = s) : ↥(D S F γ q s) := ⟨κ p S F γ hγ q u t', h ▸ κ_mem p S F γ hγ q u t'⟩

lemma φh_ψh (t'' : T'[q]) (h : (u : Γ) • t' = t'') (s : T[q]) (h₁ : π p S F q t' = s) (h₂ : π p S F q t'' = s)
    (d : ↥(D' p S F γ hγ q t'')) :
    φh p S F γ hγ q t' s h₁ (ψh p S F γ hγ q u t' t'' h d) =
      (κ' p S F γ hγ q u t' s h₁)⁻¹ * φh p S F γ hγ q t'' s h₂ d * κ' p S F γ hγ q u t' s h₁ := by
  subst h
  apply Subtype.ext
  simp only [coe_φh, coe_ψh, Subgroup.coe_mul, Subgroup.coe_inv, κ']
  have e := gg_mul_uu p S F γ hγ q u t'
  have e' : (gg p S F γ hγ q u t')⁻¹ = uu p S F γ hγ q t' * (κ p S F γ hγ q u t')⁻¹ *
      (uu p S F γ hγ q ((u : Γ) • t') : Γ)⁻¹ := by
    have : gg p S F γ hγ q u t' = uu p S F γ hγ q ((u : Γ) • t') * κ p S F γ hγ q u t' * (uu p S F γ hγ q t' : Γ)⁻¹ := by
      rw [← e]; group
    rw [this]; group
  rw [show (uu p S F γ hγ q t' : Γ)⁻¹ * ((gg p S F γ hγ q u t')⁻¹ * ↑d * gg p S F γ hγ q u t') * ↑(uu p S F γ hγ q t') =
      (uu p S F γ hγ q t' : Γ)⁻¹ * (gg p S F γ hγ q u t')⁻¹ * ↑d * (gg p S F γ hγ q u t' * ↑(uu p S F γ hγ q t')) by group,
    e, e']
  group

end Data

section Maps

local notation "k" => ZMod p

abbrev V := ∀ (q : ↥S) (t : T[q]), continuousH2 (D S F γ q t).subtype (Tr k (D S F γ q t))
abbrev V' := ∀ (q : ↥S) (t' : T'[q]), continuousH2 (D' p S F γ hγ q t').subtype (Tr k (D' p S F γ hγ q t'))
abbrev H := continuousH2Sr (U).subtype S (Tr k U)
abbrev H' := continuousH2Sr (U').subtype S (Tr k U')

lemma D_le (q : ↥S) (t : T[q]) : D S F γ q t ≤ U := inf_le_left
lemma D'_le (q : ↥S) (t' : T'[q]) : D' p S F γ hγ q t' ≤ U' := inf_le_left

def loc (x : H p S F) : V p S F γ := fun q t => mixPull k S (Subgroup.inclusion (D_le S F γ q t)) (isConj_inclusion _) x
def loc' (x' : H' p S F) : V' p S F γ hγ :=
  fun q t' => mixPull k S (Subgroup.inclusion (D'_le p S F γ hγ q t')) (isConj_inclusion _) x'

def resH (x : H p S F) : H' p S F := conjPullS k S (Subgroup.inclusion (U'_le p F)) (isConj_inclusion _) x

def resLoc (y : V p S F γ) : V' p S F γ hγ :=
  fun q t' => conjPull k (φh p S F γ hγ q t' (π p S F q t') rfl) (isConj_φh p S F γ hγ q t' _ rfl) (y q (π p S F q t'))

def cLoc (u : ↥U) (y' : V' p S F γ hγ) : V' p S F γ hγ :=
  fun q t'' => conjPull k (ψh p S F γ hγ q u ((u : Γ)⁻¹ • t'') t'' (smul_inv_smul _ _))
    (isConj_ψh p S F γ hγ q u _ t'' _) (y' q ((u : Γ)⁻¹ • t''))

def cj (A : Subgroup Γ) (g : Γ) (hg : ∀ a ∈ A, g⁻¹ * a * g ∈ A) : ↥A →* ↥A where
  toFun a := ⟨g⁻¹ * a * g, hg a a.2⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' a b := by apply Subtype.ext; simp only [Subgroup.coe_mul]; group

lemma coe_cj (A : Subgroup Γ) (g : Γ) (hg : ∀ a ∈ A, g⁻¹ * a * g ∈ A) (a : ↥A) : (cj A g hg a : Γ) = g⁻¹ * a * g := rfl

lemma isConj_cj (A : Subgroup Γ) (g : Γ) (hg : ∀ a ∈ A, g⁻¹ * a * g ∈ A) : IsConj (cj A g hg) := ⟨g, fun _ => rfl⟩

lemma cj_mem_U' (g : Γ) : ∀ a ∈ U', g⁻¹ * a * g ∈ U' := fun a ha => (normal_U' p F).conj_mem' _ ha _
lemma cj_mem_U (g : Γ) : ∀ a ∈ U, g⁻¹ * a * g ∈ U := fun a ha => (normal_U F).conj_mem' _ ha _

def cH (u : ↥U) (x' : H' p S F) : H' p S F := conjPullS k S (cj U' (u : Γ) (cj_mem_U' p F u)) (isConj_cj _ _ _) x'

lemma resLoc_reindex (y : V p S F γ) (q : ↥S) (t' : T'[q]) (s₁ s₂ : T[q]) (h₁ : π p S F q t' = s₁) (h₂ : π p S F q t' = s₂) :
    conjPull k (φh p S F γ hγ q t' s₁ h₁) (isConj_φh p S F γ hγ q t' s₁ h₁) (y q s₁) =
      conjPull k (φh p S F γ hγ q t' s₂ h₂) (isConj_φh p S F γ hγ q t' s₂ h₂) (y q s₂) := by
  subst h₁; subst h₂; rfl

lemma cLoc_resLoc (u : ↥U) (y : V p S F γ) : cLoc p S F γ hγ u (resLoc p S F γ hγ y) = resLoc p S F γ hγ y := by
  funext q t''
  simp only [cLoc, resLoc]
  set t' : T'[q] := (u : Γ)⁻¹ • t'' with ht'
  have h : (u : Γ) • t' = t'' := smul_inv_smul _ _
  have h₁ : π p S F q t' = π p S F q t'' := by rw [← h, π_smul]
  have hκ := (κ' p S F γ hγ q u t' _ h₁).2
  let ι : ↥(D S F γ q (π p S F q t'')) →* ↥(D S F γ q (π p S F q t'')) :=
    cj (D S F γ q (π p S F q t'')) (κ p S F γ hγ q u t')
      (fun a ha => Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hκ) ha) hκ)
  have hι : IsConj ι := isConj_cj _ _ _
  have hcomp : ∀ d, ((φh p S F γ hγ q t' _ h₁).comp (ψh p S F γ hγ q u t' t'' h)) d =
      (ι.comp (φh p S F γ hγ q t'' (π p S F q t'') rfl)) d := by
    intro d
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, φh_ψh p S F γ hγ q u t' t'' h _ h₁ rfl]
    rfl
  rw [resLoc_reindex p S F γ hγ y q t' _ _ rfl h₁,
    conjPull_conjPull k _ _ _ _ ((isConj_φh p S F γ hγ q t' _ h₁).comp' (isConj_ψh p S F γ hγ q u t' t'' h)),
    conjPull_congr k _ _ _ (hι.comp' (isConj_φh p S F γ hγ q t'' _ rfl)) hcomp,
    ← conjPull_conjPull k _ (isConj_φh p S F γ hγ q t'' _ rfl) ι hι,
    conjPull_inner k (κ' p S F γ hγ q u t' _ h₁) ι (fun a => rfl) hι]

lemma cLoc_loc' (u : ↥U) (x' : H' p S F) : cLoc p S F γ hγ u (loc' p S F γ hγ x') = loc' p S F γ hγ (cH p S F u x') := by
  funext q t''
  simp only [cLoc, loc', cH]
  set t' : T'[q] := (u : Γ)⁻¹ • t'' with ht'
  have h : (u : Γ) • t' = t'' := smul_inv_smul _ _

  let ι : ↥U' →* ↥U' := cj U' (ω' p S F γ hγ q u t')⁻¹ (cj_mem_U' p F _)
  have hι : IsConj ι := isConj_cj _ _ _
  have hcomp : ∀ d, ((Subgroup.inclusion (D'_le p S F γ hγ q t')).comp (ψh p S F γ hγ q u t' t'' h)) d =
      ((cj U' (u : Γ) (cj_mem_U' p F u)).comp (ι.comp (Subgroup.inclusion (D'_le p S F γ hγ q t'')))) d := by
    intro d
    apply Subtype.ext
    dsimp only [ι]
    simp only [MonoidHom.comp_apply, Subgroup.coe_inclusion, coe_ψh, coe_cj, gg, inv_inv, mul_inv_rev]
    group
  rw [conjPull_mixPull k S _ _ _ _ ((isConj_inclusion _).comp' (isConj_ψh p S F γ hγ q u t' t'' h)),
    mixPull_congr k S _ _ _ ((isConj_cj _ _ _).comp' (hι.comp' (isConj_inclusion _))) hcomp,
    ← mixPull_conjPullS k S _ (hι.comp' (isConj_inclusion _)) _ (isConj_cj _ _ _),
    ← mixPull_conjPullS k S _ (isConj_inclusion _) ι hι,
    conjPullS_inner k S ⟨(ω' p S F γ hγ q u t')⁻¹, Subgroup.inv_mem _ (ω'_mem p S F γ hγ q u t')⟩ ι (fun a => ?_) hι]
  apply Subtype.ext
  dsimp only [ι]
  simp only [coe_cj, inv_inv, Subgroup.coe_mul, Subgroup.coe_inv]

lemma cH_mul (u v : ↥U) (x' : H' p S F) : cH p S F (u * v) x' = cH p S F u (cH p S F v x') := by
  simp only [cH]
  rw [conjPullS_conjPullS k S _ _ _ _ ((isConj_cj _ _ _).comp' (isConj_cj _ _ _))]
  refine conjPullS_congr k S _ _ _ _ (fun a => ?_) x'
  apply Subtype.ext
  simp only [coe_cj, MonoidHom.comp_apply, Subgroup.coe_mul, mul_inv_rev]
  group

lemma cH_of_mem (u : ↥U) (hu : (u : Γ) ∈ U') (x' : H' p S F) : cH p S F u x' = x' :=
  conjPullS_inner k S ⟨(u : Γ), hu⟩ _ (fun _ => rfl) _ x'

lemma cH_resH (u : ↥U) (x : H p S F) : cH p S F u (resH p S F x) = resH p S F x := by
  simp only [cH, resH]
  have hcomp : ∀ a, ((Subgroup.inclusion (U'_le p F)).comp (cj U' (u : Γ) (cj_mem_U' p F u))) a =
      ((cj U (u : Γ) (cj_mem_U F u)).comp (Subgroup.inclusion (U'_le p F))) a := fun a => Subtype.ext rfl
  rw [conjPullS_conjPullS k S _ _ _ _ ((isConj_inclusion _).comp' (isConj_cj _ _ _)),
    conjPullS_congr k S _ _ _ ((isConj_cj _ _ _).comp' (isConj_inclusion _)) hcomp,
    ← conjPullS_conjPullS k S _ (isConj_inclusion _) _ (isConj_cj _ _ _),
    conjPullS_inner k S u _ (fun a => rfl) (isConj_cj _ _ _)]

lemma loc'_resH (x : H p S F) : loc' p S F γ hγ (resH p S F x) = resLoc p S F γ hγ (loc p S F γ x) := by
  funext q t'
  simp only [loc', resH, resLoc, loc]
  have hcomp : ∀ d, ((Subgroup.inclusion (D_le S F γ q (π p S F q t'))).comp (φh p S F γ hγ q t' _ rfl)) d =
      ((cj U (uu p S F γ hγ q t' : Γ) (cj_mem_U F _)).comp
        ((Subgroup.inclusion (U'_le p F)).comp (Subgroup.inclusion (D'_le p S F γ hγ q t')))) d :=
    fun d => Subtype.ext rfl
  rw [mixPull_conjPullS k S _ _ _ _ ((isConj_inclusion _).comp' (isConj_inclusion _)),
    conjPull_mixPull k S _ _ _ _ ((isConj_inclusion _).comp' (isConj_φh p S F γ hγ q t' _ rfl)),
    mixPull_congr k S _ _ _ ((isConj_cj _ _ _).comp' ((isConj_inclusion _).comp' (isConj_inclusion _))) hcomp,
    ← mixPull_conjPullS k S _ ((isConj_inclusion _).comp' (isConj_inclusion _)) _ (isConj_cj _ _ _),
    conjPullS_inner k S (uu p S F γ hγ q t') _ (fun a => rfl) (isConj_cj _ _ _)]

include hF in
lemma conjPull_φh_injective (q : ↥S) (t' : T'[q]) (s : T[q]) (h : π p S F q t' = s) :
    Function.Injective (conjPull k (φh p S F γ hγ q t' s h) (isConj_φh p S F γ hγ q t' s h)) := by
  haveI := hF.1

  let Ds : Subgroup Γ := D S F γ q s
  let Ssub : Subgroup ↥Ds := (Fz p F).fixingSubgroup.comap Ds.subtype
  haveI : Ssub.FiniteIndex := groupCohomology.finiteIndex_comap_fixingSubgroup Ds.subtype (Fz p F)
  have hu : IsUnit (((Ssub.index : ℕ)) : k) := (isUnit_index_of_le p F Ds (D_le S F γ q s)).2
  have hres := groupCohomology.continuousH2Map_res_injective_of_isUnit_index Ds.subtype Ssub
    ⟨Fz p F, inferInstance, le_rfl⟩ hu (Tr k Ds)
  let SΓ : Subgroup Γ := Ds ⊓ U'
  let inclD : ↥SΓ →* ↥Ds := Subgroup.inclusion inf_le_left
  let j : ↥SΓ →* ↥Ssub :=
    { toFun := fun x => ⟨⟨x, x.2.1⟩, x.2.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl }
  let j' : ↥Ssub →* ↥SΓ :=
    { toFun := fun y => ⟨y.1.1, ⟨y.1.2, y.2⟩⟩, map_one' := rfl, map_mul' := fun _ _ => rfl }
  let J : continuousH2 (Ds.subtype.comp Ssub.subtype) (Rep.res Ssub.subtype (Tr k Ds)) →ₗ[k]
      continuousH2 SΓ.subtype (Tr k SΓ) :=
    continuousH2Map (rH := Ds.subtype.comp Ssub.subtype) (rG := SΓ.subtype) (A := Rep.res Ssub.subtype (Tr k Ds))
      (B := Tr k SΓ) j (fun _ => rfl) LinearMap.id (fun _ _ => rfl)
  let J' : continuousH2 SΓ.subtype (Tr k SΓ) →ₗ[k] continuousH2 (Ds.subtype.comp Ssub.subtype) (Rep.res Ssub.subtype (Tr k Ds)) :=
    continuousH2Map (rH := SΓ.subtype) (rG := Ds.subtype.comp Ssub.subtype) (A := Tr k SΓ)
      (B := Rep.res Ssub.subtype (Tr k Ds)) j' (fun _ => rfl) LinearMap.id (fun _ _ => rfl)
  have hJ : Function.Injective J := by
    refine Function.LeftInverse.injective (g := J') fun x => ?_
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ x
    rfl

  let e : ↥(D' p S F γ hγ q t') →* ↥SΓ :=
    { toFun := fun d => ⟨(uu p S F γ hγ q t' : Γ)⁻¹ * d * uu p S F γ hγ q t',
        ⟨(φh p S F γ hγ q t' s h d).2, (normal_U' p F).conj_mem' _ d.2.1 _⟩⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := fun a b => by apply Subtype.ext; simp only [Subgroup.coe_mul]; group }
  have he : IsConj e := ⟨uu p S F γ hγ q t', fun _ => rfl⟩
  let e' : ↥SΓ →* ↥(D' p S F γ hγ q t') :=
    { toFun := fun x => ⟨(uu p S F γ hγ q t' : Γ) * x * (uu p S F γ hγ q t' : Γ)⁻¹, by
        refine ⟨(normal_U' p F).conj_mem _ x.2.2 _, ?_⟩
        have hx := x.2.1.2
        subst h
        change (x : Γ) ∈ (K[q]).map (MulAut.conj (γ q (π p S F q t'))).toMonoidHom at hx
        change _ ∈ (K[q]).map (MulAut.conj (γ' p S F γ hγ q t')).toMonoidHom
        rw [γ', map_conj_mul]
        exact ⟨x, hx, rfl⟩⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := fun a b => by apply Subtype.ext; simp only [Subgroup.coe_mul]; group }
  have he' : IsConj e' := ⟨(uu p S F γ hγ q t' : Γ)⁻¹, fun _ => by simp only [inv_inv]; rfl⟩
  have hee' : Function.Injective (conjPull k e he) := by
    refine Function.LeftInverse.injective (g := conjPull k e' he') fun x => ?_
    rw [conjPull_conjPull k _ _ _ _ (he.comp' he'),
      conjPull_congr k _ (MonoidHom.id _) _ ⟨1, fun a => by simp⟩ (fun a => ?_), conjPull_id]
    apply Subtype.ext
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply]
    change (uu p S F γ hγ q t' : Γ)⁻¹ * ((uu p S F γ hγ q t' : Γ) * a * (uu p S F γ hγ q t' : Γ)⁻¹) * uu p S F γ hγ q t' = a
    group

  have hfac : ∀ x, conjPull k (φh p S F γ hγ q t' s h) (isConj_φh p S F γ hγ q t' s h) x =
      conjPull k e he (J (groupCohomology.continuousH2Map (rH := Ds.subtype) (rG := Ds.subtype.comp Ssub.subtype)
        (A := Tr k Ds) (B := Rep.res Ssub.subtype (Tr k Ds)) Ssub.subtype (fun _ => rfl) LinearMap.id (fun _ _ => rfl) x)) := by
    intro x
    have h1 : conjPull k inclD (isConj_inclusion _) x =
        J (groupCohomology.continuousH2Map (rH := Ds.subtype) (rG := Ds.subtype.comp Ssub.subtype)
          (A := Tr k Ds) (B := Rep.res Ssub.subtype (Tr k Ds)) Ssub.subtype (fun _ => rfl) LinearMap.id (fun _ _ => rfl) x) := by
      obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ x
      rfl
    rw [← h1, conjPull_conjPull k _ _ _ _ ((isConj_inclusion _).comp' he)]
    exact conjPull_congr k _ _ _ _ (fun d => Subtype.ext rfl) x
  intro a b hab
  exact hres (hJ (hee' ((hfac a).symm.trans (hab.trans (hfac b)))))

include hF in
lemma resLoc_eq_zero {y : V p S F γ} (hy : resLoc p S F γ hγ y = 0) : y = 0 := by
  funext q s
  obtain ⟨g, hg⟩ : ∃ g : Γ, (g : T[q]) = s := ⟨s.out, QuotientGroup.out_eq' s⟩
  have h : π p S F q (g : T'[q]) = s := by rw [π_mk, hg]
  have h0 := congrFun (congrFun hy q) (g : T'[q])
  simp only [resLoc, Pi.zero_apply] at h0
  rw [resLoc_reindex p S F γ hγ y q _ _ s rfl h] at h0
  rw [Pi.zero_apply, Pi.zero_apply]
  exact conjPull_φh_injective p S F hF γ hγ q _ s h (h0.trans (map_zero _).symm)

lemma cLoc_add (u : ↥U) (a b : V' p S F γ hγ) : cLoc p S F γ hγ u (a + b) = cLoc p S F γ hγ u a + cLoc p S F γ hγ u b := by
  funext q t'; simp only [cLoc, Pi.add_apply, map_add]
lemma cLoc_smul (u : ↥U) (c : k) (a : V' p S F γ hγ) : cLoc p S F γ hγ u (c • a) = c • cLoc p S F γ hγ u a := by
  funext q t'; simp only [cLoc, Pi.smul_apply, map_smul]
lemma cH_smul (u : ↥U) (c : k) (a : H' p S F) : cH p S F u (c • a) = c • cH p S F u a := map_smul _ _ _
lemma cH_sum (u : ↥U) {ι : Type} (T : Finset ι) (f : ι → H' p S F) :
    cH p S F u (∑ i ∈ T, f i) = ∑ i ∈ T, cH p S F u (f i) := map_sum _ _ _

abbrev Nsub : Subgroup ↥U := (U').subgroupOf U

scoped instance normal_Nsub : (Nsub p F).Normal := Subgroup.normal_subgroupOf
scoped instance finiteIndex_Nsub : (Nsub p F).FiniteIndex := (isUnit_index_of_le p F U le_rfl).1
lemma isUnit_index_Nsub : IsUnit ((((Nsub p F).index : ℕ)) : k) := (isUnit_index_of_le p F U le_rfl).2

abbrev QQ : Type := ↥U ⧸ Nsub p F

set_option hygiene false in
local notation "Q" => QQ p F

scoped instance fintypeQ : Fintype Q := Fintype.ofFinite _

lemma card_Q : (Fintype.card Q : k) ≠ 0 := by
  rw [← Nat.card_eq_fintype_card]
  exact (isUnit_index_Nsub p F).ne_zero

lemma cH_out_mk_mul (v : ↥U) (r : Q) (x' : H' p S F) :
    cH p S F ((QuotientGroup.mk v * r).out) x' = cH p S F v (cH p S F r.out x') := by
  have h : (((QuotientGroup.mk v * r).out : ↥U) : Q) = ((v * r.out : ↥U) : Q) := by
    rw [QuotientGroup.out_eq', QuotientGroup.mk_mul, QuotientGroup.out_eq']
  rw [QuotientGroup.eq] at h
  have hn : (((QuotientGroup.mk v * r).out⁻¹ * (v * r.out) : ↥U) : Γ) ∈ U' := h
  have : v * r.out = (QuotientGroup.mk v * r).out * ((QuotientGroup.mk v * r).out⁻¹ * (v * r.out)) := by group
  rw [← cH_mul, this, cH_mul, cH_of_mem p S F _ hn]

lemma cH_sum_out (v : ↥U) (x' : H' p S F) :
    cH p S F v (∑ r : Q, cH p S F r.out x') = ∑ r : Q, cH p S F r.out x' := by
  rw [cH_sum]
  simp_rw [← cH_out_mk_mul]
  exact Fintype.sum_equiv (Equiv.mulLeft (QuotientGroup.mk v)) _ _ (fun _ => rfl)

include hpS hF in
lemma exists_resH_eq (xb : H' p S F) (hinv : ∀ v : ↥U, cH p S F v xb = xb) : ∃ x : H p S F, resH p S F x = xb := by
  obtain ⟨X, rfl⟩ := Submodule.mkQ_surjective _ xb
  let e : ↥(Nsub p F) ≃* ↥U' := Subgroup.subgroupOfEquivOfLe (U'_le p F)

  let XN : ↥(Nsub p F) × ↥(Nsub p F) → k := (X : ↥U' × ↥U' → k) ∘ Prod.map e e
  have hXN : XN ∈ levelCocyclesSr₂ ((U).subtype.comp (Nsub p F).subtype) S (Rep.res (Nsub p F).subtype (Tr k U)) :=
    cochainsPullPush₂_mem_levelCocyclesSr₂ (rH := (U').subtype) (rG := (U).subtype.comp (Nsub p F).subtype)
      (A := Tr k U') (B := Rep.res (Nsub p F).subtype (Tr k U)) e.toMonoidHom (fun _ => rfl) S LinearMap.id
      (fun _ _ => rfl) X.2
  have hinvN : ∀ g : ↥U,
      (fun ab : ↥(Nsub p F) × ↥(Nsub p F) =>
        (Tr k U).ρ g (XN (MulAut.conjNormal g⁻¹ ab.1, MulAut.conjNormal g⁻¹ ab.2))) - XN ∈
      levelCoboundariesSr₂ ((U).subtype.comp (Nsub p F).subtype) S (Rep.res (Nsub p F).subtype (Tr k U)) := by
    intro g
    have h1 := hinv g
    change conjPullS k S _ _ (continuousH2Srπ _ _ _ X) = continuousH2Srπ _ _ _ X at h1
    rw [conjPullS_mk] at h1
    have h2 : cochainsPullPush₂ (A := Tr k U') (B := Tr k U') (cj U' (g : Γ) (cj_mem_U' p F g)) LinearMap.id X.1 - X.1 ∈
        levelCoboundariesSr₂ (U').subtype S (Tr k U') := (πS_eq_iff _ _ _ _ _).1 h1
    have h3 := cochainsPullPush₂_mem_levelCoboundariesSr₂ (rH := (U').subtype) (rG := (U).subtype.comp (Nsub p F).subtype)
      (A := Tr k U') (B := Rep.res (Nsub p F).subtype (Tr k U)) e.toMonoidHom (fun _ => rfl) S LinearMap.id
      (fun _ _ => rfl) h2
    have hc : ∀ n : ↥(Nsub p F), e (MulAut.conjNormal g⁻¹ n) = cj U' (g : Γ) (cj_mem_U' p F g) (e n) := by
      intro n
      apply Subtype.ext
      change (((MulAut.conjNormal g⁻¹ n : ↥(Nsub p F)) : ↥U) : Γ) = (g : Γ)⁻¹ * n * g
      rw [MulAut.conjNormal_apply, inv_inv]; rfl
    convert h3 using 1 <;> first | rfl | exact Subsingleton.elim _ _

  obtain ⟨y, hy, hyX⟩ :=
    groupCohomology.exists_mem_levelCocyclesSr2_res_sub_mem_levelCoboundariesSr2_of_isUnit_index
      (U).subtype S (Tr k U) (fun _ => ⟨⊥, IntermediateField.isUnramifiedOutside_bot S, fun _ _ => rfl⟩)
      (Nsub p F) (isUnit_index_Nsub p F) ⟨Fz p F, isUnramifiedOutside_Fz p F S hpS hF, le_rfl⟩ XN hXN hinvN
  refine ⟨continuousH2Srπ _ _ _ ⟨y, hy⟩, ?_⟩
  change conjPullS k S _ _ (continuousH2Srπ _ _ _ ⟨y, hy⟩) = continuousH2Srπ _ _ _ X
  rw [conjPullS_mk]
  apply (πS_eq_iff _ _ _ _ _).2

  have h4 := cochainsPullPush₂_mem_levelCoboundariesSr₂ (rH := (U).subtype.comp (Nsub p F).subtype) (rG := (U').subtype)
      (A := Rep.res (Nsub p F).subtype (Tr k U)) (B := Tr k U') e.symm.toMonoidHom (fun _ => rfl) S LinearMap.id
      (fun _ _ => rfl) hyX
  convert h4 using 1 <;> first | rfl | exact Subsingleton.elim _ _

include hpS hF in

lemma exists_resLoc_eq (w' : V' p S F γ hγ)
    (hw' : ∀ y' : V' p S F γ hγ, ∃ (x' : H' p S F) (c : k), ∀ q t', y' q t' = loc' p S F γ hγ x' q t' + c • w' q t')
    (wb : V' p S F γ hγ) (hwb : ∀ q t', wb q t' = (Fintype.card Q : k)⁻¹ • ∑ r : Q, cLoc p S F γ hγ r.out w' q t')
    (y : V p S F γ) :
    ∃ (x : H p S F) (c : k), ∀ q t', resLoc p S F γ hγ y q t' = resLoc p S F γ hγ (loc p S F γ x) q t' + c • wb q t' := by
  classical
  obtain ⟨x', c, hxc⟩ := hw' (resLoc p S F γ hγ y)
  have hy' : resLoc p S F γ hγ y = loc' p S F γ hγ x' + c • w' := funext fun q => funext fun t' => hxc q t'

  have hu : ∀ u : ↥U, resLoc p S F γ hγ y = loc' p S F γ hγ (cH p S F u x') + c • cLoc p S F γ hγ u w' := by
    intro u
    rw [← cLoc_loc', ← cLoc_smul, ← cLoc_add, ← hy', cLoc_resLoc]

  let xb : H' p S F := (Fintype.card Q : k)⁻¹ • ∑ r : Q, cH p S F r.out x'
  have hA : ∀ q t', resLoc p S F γ hγ y q t' = loc' p S F γ hγ xb q t' + c • wb q t' := by
    intro q t'
    have hsum : ∑ _r : Q, resLoc p S F γ hγ y q t' =
        ∑ r : Q, (loc' p S F γ hγ (cH p S F r.out x') q t' + c • cLoc p S F γ hγ r.out w' q t') :=
      Finset.sum_congr rfl fun r _ => congrFun (congrFun (hu r.out) q) t'
    rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul k, Finset.sum_add_distrib, ← Finset.smul_sum] at hsum
    have hl : ∑ r : Q, loc' p S F γ hγ (cH p S F r.out x') q t' = loc' p S F γ hγ (∑ r : Q, cH p S F r.out x') q t' :=
      (map_sum (mixPull k S (Subgroup.inclusion (D'_le p S F γ hγ q t')) (isConj_inclusion _)) _ _).symm
    rw [hl] at hsum
    have hc0 := card_Q p F
    have := congrArg (fun v => (Fintype.card Q : k)⁻¹ • v) hsum
    simp only [smul_smul, inv_mul_cancel₀ hc0, one_smul, smul_add] at this
    rw [this, hwb]
    change _ = mixPull k S _ _ ((Fintype.card Q : k)⁻¹ • ∑ r : Q, cH p S F r.out x') + _
    rw [map_smul, smul_smul, mul_comm c]
    rfl

  have hinv : ∀ v : ↥U, cH p S F v xb = xb := by
    intro v
    simp only [xb, cH_smul, cH_sum_out]
  obtain ⟨x, hx⟩ := exists_resH_eq p S hpS F hF xb hinv
  refine ⟨x, c, fun q t' => ?_⟩
  rw [hA, ← hx, loc'_resH]

lemma resLoc_apply (z : V p S F γ) (q : ↥S) (t' : T'[q]) : resLoc p S F γ hγ z q t' =
    conjPull k (φh p S F γ hγ q t' _ rfl) (isConj_φh p S F γ hγ q t' _ rfl) (z q (π p S F q t')) := rfl

include hγ hpS hF in
theorem descent (h4 : p = 2 → ∃ i ∈ F, i ^ 2 = -1) :
    ∃ w : V p S F γ, ∀ y : V p S F γ, ∃ (x : H p S F) (c : k), ∀ q t, y q t = loc p S F γ x q t + c • w q t := by
  classical
  haveI := hF.1

  obtain ⟨w', hw'⟩ := core_zeta p S hpS (Fz p F) (isUnramifiedOutside_Fz p F S hpS hF)
    (fun σ hσ => smul_zeta_of_mem p F hσ) (γ' p S F γ hγ) (hγ' p S F γ hγ)
    (fun h2 => (h4 h2).imp fun i hi => ⟨le_Fz p F hi.1, hi.2⟩)

  obtain ⟨wb, hwb⟩ : ∃ wb : V' p S F γ hγ, ∀ q t', wb q t' = (Fintype.card Q : k)⁻¹ • ∑ r : Q, cLoc p S F γ hγ r.out w' q t' :=
    ⟨_, fun _ _ => rfl⟩
  have claimA := exists_resLoc_eq p S hpS F hF γ hγ w' hw' wb hwb

  by_cases hex : ∃ (y₀ : V p S F γ) (x₀ : H p S F) (c₀ : k), c₀ ≠ 0 ∧
      ∀ q t', resLoc p S F γ hγ y₀ q t' = resLoc p S F γ hγ (loc p S F γ x₀) q t' + c₀ • wb q t'
  · obtain ⟨y₀, x₀, c₀, hc₀, h₀⟩ := hex
    refine ⟨fun q t => c₀⁻¹ • (y₀ q t - loc p S F γ x₀ q t), fun y => ?_⟩
    obtain ⟨x, c, hxc⟩ := claimA y
    refine ⟨x, c, ?_⟩
    have h0 : resLoc p S F γ hγ (fun q t => y q t - (loc p S F γ x q t + c • (c₀⁻¹ • (y₀ q t - loc p S F γ x₀ q t)))) = 0 := by
      funext q t'
      rw [resLoc_apply, Pi.zero_apply, Pi.zero_apply, map_sub, map_add, map_smul, map_smul, map_sub, ← resLoc_apply,
        ← resLoc_apply, ← resLoc_apply, ← resLoc_apply, hxc, h₀, add_sub_cancel_left, inv_smul_smul₀ hc₀, sub_self]
    intro q t
    exact eq_of_sub_eq_zero (congrFun (congrFun (resLoc_eq_zero p S F hF γ hγ h0) q) t)
  · refine ⟨0, fun y => ?_⟩
    obtain ⟨x, c, hxc⟩ := claimA y
    refine ⟨x, 0, ?_⟩
    have hc : c = 0 := by
      by_contra hc
      exact hex ⟨y, x, c, hc, hxc⟩
    subst hc
    have h0 : resLoc p S F γ hγ (fun q t => y q t - loc p S F γ x q t) = 0 := by
      funext q t'
      have := hxc q t'
      rw [zero_smul, add_zero] at this
      rw [resLoc_apply, Pi.zero_apply, Pi.zero_apply, map_sub, ← resLoc_apply, ← resLoc_apply, this, sub_self]
    intro q t
    rw [zero_smul, add_zero]
    exact eq_of_sub_eq_zero (congrFun (congrFun (resLoc_eq_zero p S F hF γ hγ h0) q) t)

end Maps

end Descent

end P2MW1cG
p2m_reactivate "P2MW.S_groupCohomology_exists_forall_eq_res_continuousH2Sr_trivial_add_smul_of_exists_sq_eq_neg_one.P2MW1cG"

open P2MW1cG in
theorem solution
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [IsGalois ℚ F] (hF : F.IsUnramifiedOutside S)
    (h4 : p = 2 → ∃ i ∈ F, i ^ 2 = -1)
    (γ : ∀ q : ↥S, (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ (F.fixingSubgroup ⊔ (extArithLoc S (Sum.inr q)).range) →
      (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (hγ : ∀ q t, (γ q t : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ (F.fixingSubgroup ⊔ (extArithLoc S (Sum.inr q)).range)) = t) :
    ∃ w : ∀ (q : ↥S) (t : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ (F.fixingSubgroup ⊔ (extArithLoc S (Sum.inr q)).range)),
        continuousH2 (F.fixingSubgroup ⊓ ((extArithLoc S (Sum.inr q)).range.map (MulAut.conj (γ q t)).toMonoidHom)).subtype
          (Rep.trivial (ZMod p) ↥(F.fixingSubgroup ⊓ ((extArithLoc S (Sum.inr q)).range.map (MulAut.conj (γ q t)).toMonoidHom)) (ZMod p)),
      ∀ y : ∀ (q : ↥S) (t : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ (F.fixingSubgroup ⊔ (extArithLoc S (Sum.inr q)).range)),
        continuousH2 (F.fixingSubgroup ⊓ ((extArithLoc S (Sum.inr q)).range.map (MulAut.conj (γ q t)).toMonoidHom)).subtype
          (Rep.trivial (ZMod p) ↥(F.fixingSubgroup ⊓ ((extArithLoc S (Sum.inr q)).range.map (MulAut.conj (γ q t)).toMonoidHom)) (ZMod p)),
        ∃ (x : continuousH2Sr F.fixingSubgroup.subtype S (Rep.trivial (ZMod p) ↥F.fixingSubgroup (ZMod p))) (c : ZMod p),
          ∀ q t, y q t =
            continuousH2Map (rH := F.fixingSubgroup.subtype)
                (rG := (F.fixingSubgroup ⊓ ((extArithLoc S (Sum.inr q)).range.map (MulAut.conj (γ q t)).toMonoidHom)).subtype)
                (Subgroup.inclusion inf_le_left) (fun _ => rfl)
                (LinearMap.id : Rep.trivial (ZMod p) ↥F.fixingSubgroup (ZMod p) →ₗ[ZMod p]
                  Rep.trivial (ZMod p) ↥(F.fixingSubgroup ⊓ ((extArithLoc S (Sum.inr q)).range.map (MulAut.conj (γ q t)).toMonoidHom)) (ZMod p))
                (fun _ _ => rfl)
                (continuousH2SrToContinuousH2 F.fixingSubgroup.subtype S (Rep.trivial (ZMod p) ↥F.fixingSubgroup (ZMod p)) x)
              + c • w q t := by
  obtain ⟨w, hw⟩ := descent p S hpS F hF γ hγ h4
  refine ⟨w, fun y => ?_⟩
  obtain ⟨x, c, hxc⟩ := hw y
  refine ⟨x, c, fun q t => ?_⟩
  exact (hxc q t).trans (congrArg₂ (· + ·) (loc_eq_mixPull (ZMod p) S _ (isConj_inclusion _) x).symm rfl)

end
end S_groupCohomology_exists_forall_eq_res_continuousH2Sr_trivial_add_smul_of_exists_sq_eq_neg_one
end P2MW
export P2MW.S_groupCohomology_exists_forall_eq_res_continuousH2Sr_trivial_add_smul_of_exists_sq_eq_neg_one (solution)
