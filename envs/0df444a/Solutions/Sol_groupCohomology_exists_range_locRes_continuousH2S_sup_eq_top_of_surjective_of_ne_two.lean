-- Prove2me | solution 1 for groupCohomology.exists_range_locRes_continuousH2S_sup_eq_top_of_surjective_of_ne_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/5d15156d-7f22-514f-a07b-2e3856babd46

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_GroupCohomology_ContinuousDuality
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_GroupCohomology_LocalInvariant
import Definitions.Def_GroupCohomology_ContinuousH2Map
import Definitions.Def_GroupCohomology_ContinuousH1
import Theorems.Thm_groupCohomology_bijective_theta_dualTwist_of_primeLocal
import Theorems.Thm_groupCohomology_exists_theta0_and_theta2
import Theorems.Thm_groupCohomology_exists_theta1
import Theorems.Thm_groupCohomology_isLocalInv_localInv_and_bijective
import Theorems.Thm_groupCohomology_exists_level_ofChar_cycloChar_comp
import Theorems.Thm_groupCohomology_continuousH2MapHom_surjective_of_surjective_of_primeLocal
import Theorems.Thm_groupCohomology_sum_localInv_locRes2S_eq_zero_of_ne_two
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_exists_range_locRes_continuousH2S_sup_eq_top_of_surjective_of_ne_two
p2m_attr_erase "instance" "ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal groupCohomology.normal_comap_fixingSubgroup groupCohomology.finiteIndex_comap_fixingSubgroup ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete groupCohomology.Kummer.instMulDistribMulActionRootsOfUnity M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion NumberField.AdelicHaar.locallyCompactSpace_adeleRing NumberField.AdelicHaar.finite_residueField_adicCompletionIntegers NumberField.AdelicHaar.locallyCompactSpace_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_finiteAdeleRing NumberField.AdelicHaar.compactSpace_adicCompletionIntegers NumberField.AdelicHaar.t2Space_finiteAdeleRing NumberField.AdelicHaar.t2Space_matrix_adeleRing NumberField.AdelicHaar.t2Space_adeleRing NumberField.AdelicHaar.fact_isOpen_adicCompletionIntegers"
p2m_attr_erase "instance" "NumberField.AdelicHaar.t2Space_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_matrix_adeleRing NumberField.AdelicHaar.t2Space_infiniteAdeleRing NumberField.AdelicHaar.properSpace_adicCompletion M4aHerbrand.Bridge.instT2SpaceAdeleRing LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite Deep.NTSupply.instNormalRayClassSubgroup instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "ExtCitation.LocalLevel.coe_smul_OO WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply groupCohomology.Kummer.coe_kummerCocycleRoots groupCohomology.Kummer.mem_powerSubgroup_iff groupCohomology.Kummer.val_smul_units groupCohomology.Kummer.kummerHom_apply groupCohomology.Kummer.coe_smul_rootsOfUnity IsLocalRing.principalUnits_zero M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk M4aHerbrand.IdeleGaloisDescent.classAct_mk M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl NumberField.SUnits.val_zsmul NumberField.SUnits.val_add M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply"
p2m_attr_erase "simp" "FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq M4aHerbrand.Bridge.finiteConorm_apply SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def"
p2m_attr_erase "simp" "TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply"
p2m_attr_erase "simp" "Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
open CategoryTheory Module groupCohomology ExtCitation

noncomputable section
namespace P2M71fOdd

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

lemma locPush_locPush_eq_zero {C : Rep k (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)}
    (ψ' : B →ₗ[k] C) (hψ' : ∀ (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (b : B), ψ' (B.ρ g b) = C.ρ g (ψ' b))
    (h0 : ∀ a, ψ' (ψ a) = 0)
    {H : Type} [Group H] (f : H →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (y : continuousH2 f (Rep.res f A)) :
    locPush ψ' hψ' f (locPush ψ hψ f y) = 0 := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  change continuousH2π f _ _ = 0
  convert (continuousH2π f (Rep.res f C)).map_zero
  refine Subtype.ext (funext fun st => ?_)
  exact h0 _

end Push

section Local

variable {p : ℕ} [Fact p.Prime]
  (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
  (hsm : ∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s ∈ F.fixingSubgroup, M.ρ s m = m)

include hsm in

lemma exists_uniform_level [FiniteDimensional (ZMod p) M] :
    ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
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

variable (q : Nat.Primes)

local notation "rq" => primeLocalToGlobal q

abbrev D₁ : Rep (ZMod p) (primeLocalGaloisGroup q) := Rep.res rq (M.dualTwist (cycloChar p))

abbrev D₂ : Rep (ZMod p) (primeLocalGaloisGroup q) := (Rep.res rq M).dualTwist ((cycloChar p).comp rq)

abbrev Nq (p : ℕ) [Fact p.Prime] (q : Nat.Primes) : Rep (ZMod p) (primeLocalGaloisGroup q) :=
  ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))

lemma D₁_ρ_eq_D₂_ρ : (D₁ M q).ρ = (D₂ M q).ρ := by
  ext g f m
  simp [Representation.twist_apply_apply]

lemma D₁_invariants_eq : (D₁ M q).ρ.invariants = (D₂ M q).ρ.invariants := by
  rw [D₁_ρ_eq_D₂_ρ]

lemma apply_ρ_of_mem_invariants (d : (D₁ M q).ρ.invariants) (g : primeLocalGaloisGroup q) (m : M) :
    (d : Dual (ZMod p) M) (M.ρ (rq g) m) = ((cycloChar p (rq g) : (ZMod p)ˣ) : ZMod p) * (d : Dual (ZMod p) M) m := by
  have h := d.2 g
  have h' := congrArg (fun f : Dual (ZMod p) M => f (M.ρ (rq g) m)) h
  simp only at h'
  rw [← h']
  simp [Representation.twist_apply_apply, Module.Dual.transpose_apply, Representation.inv_self_apply]

abbrev dLin (d : (D₁ M q).ρ.invariants) : Rep.res rq M →ₗ[ZMod p] Nq p q :=
  (d : Dual (ZMod p) M)

lemma dLin_equivariant (d : (D₁ M q).ρ.invariants) (g : primeLocalGaloisGroup q) (a : Rep.res rq M) :
    dLin M q d ((Rep.res rq M).ρ g a) = (Nq p q).ρ g (dLin M q d a) := by
  change (d : Dual (ZMod p) M) (M.ρ (rq g) a) = _
  rw [apply_ρ_of_mem_invariants]
  simp [Representation.twist_apply_apply]

def pairCocycle (z : ↥(levelCocycles₂ rq (Rep.res rq M))) (d : (D₁ M q).ρ.invariants) :
    ↥(levelCocycles₂ rq (Nq p q)) :=
  (levelCocycles₂Map (rH := rq) (rG := rq) (A := Rep.res rq M) (B := Nq p q)
    (MonoidHom.id (primeLocalGaloisGroup q)) (fun _ => rfl) (dLin M q d) (dLin_equivariant M q d)) z

@[scoped simp] lemma pairCocycle_apply (z : ↥(levelCocycles₂ rq (Rep.res rq M))) (d : (D₁ M q).ρ.invariants)
    (g : primeLocalGaloisGroup q × primeLocalGaloisGroup q) :
    (pairCocycle M q z d).1 g = (d : Dual (ZMod p) M) (z.1 g) := rfl

lemma theta2_mk_apply
    (inv : continuousH2 rq (Nq p q) →ₗ[ZMod p] ZMod p)
    (θ : continuousH2 rq (Rep.res rq M) →ₗ[ZMod p] Dual (ZMod p) (D₁ M q).ρ.invariants)
    (hθ : IsTheta2 rq (Module.Dual.eval (ZMod p) M : Rep.res rq M →ₗ[ZMod p] D₁ M q →ₗ[ZMod p] Nq p q) inv θ)
    (z : ↥(levelCocycles₂ rq (Rep.res rq M))) (d : (D₁ M q).ρ.invariants) :
    θ (continuousH2π rq (Rep.res rq M) z) d = inv (continuousH2π rq (Nq p q) (pairCocycle M q z d)) :=
  hθ z d (pairCocycle M q z d) (fun _ => rfl)

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

lemma hsm_res : ∀ m : Rep.res rq M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
    ∀ s, rq s ∈ F.fixingSubgroup → (Rep.res rq M).ρ s m = m :=
  fun m => let ⟨F, hF, h⟩ := hsm m; ⟨F, hF, fun s hs => h (rq s) hs⟩

include hsm in

lemma hsm_D₂ [FiniteDimensional (ZMod p) M] :
    ∀ x : D₂ M q, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
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

lemma eval_isEquivariantBilinear_D₂ :
    Rep.IsEquivariantBilinear (Rep.res rq M) (D₂ M q) (Nq p q)
      (Module.Dual.eval (ZMod p) M : Rep.res rq M →ₗ[ZMod p] D₂ M q →ₗ[ZMod p] Nq p q) := by
  intro g a b
  simp [Representation.twist_apply_apply, Module.Dual.transpose_apply, Representation.inv_self_apply]

lemma eval_isEquivariantBilinear_D₁ :
    Rep.IsEquivariantBilinear (Rep.res rq M) (D₁ M q) (Nq p q)
      (Module.Dual.eval (ZMod p) M : Rep.res rq M →ₗ[ZMod p] D₁ M q →ₗ[ZMod p] Nq p q) := by
  intro g a b
  simp [Representation.twist_apply_apply, Module.Dual.transpose_apply, Representation.inv_self_apply]

lemma exists_theta2 (inv : continuousH2 rq (Nq p q) →ₗ[ZMod p] ZMod p) :
    ∃ θ : continuousH2 rq (Rep.res rq M) →ₗ[ZMod p] Dual (ZMod p) (D₁ M q).ρ.invariants,
      IsTheta2 rq (Module.Dual.eval (ZMod p) M : Rep.res rq M →ₗ[ZMod p] D₁ M q →ₗ[ZMod p] Nq p q) inv θ :=
  (exists_theta0_and_theta2 (M := Rep.res rq M) (D := D₁ M q) (N := Nq p q) rq
    (Module.Dual.eval (ZMod p) M : Rep.res rq M →ₗ[ZMod p] D₁ M q →ₗ[ZMod p] Nq p q)
    (eval_isEquivariantBilinear_D₁ M q) inv).2

include hsm in

theorem bijective_theta2 [Fact ((q : ℕ)).Prime] [FiniteDimensional (ZMod p) M] (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p)
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

variable {A B : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)}
  (ψ : A →ₗ[ZMod p] B) (hψ : ∀ (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (a : A), ψ (A.ρ g a) = B.ρ g (ψ a))

include hψ in
lemma dualComp_mem (d : (D₁ B q).ρ.invariants) :
    ((d : Dual (ZMod p) B) ∘ₗ ψ : Dual (ZMod p) A) ∈ (D₁ A q).ρ.invariants := by
  intro g
  change ((cycloChar p (rq g) : (ZMod p)ˣ) : ZMod p) • (((d : Dual (ZMod p) B) ∘ₗ ψ) ∘ₗ A.ρ (rq g)⁻¹)
    = (d : Dual (ZMod p) B) ∘ₗ ψ
  have h : ((cycloChar p (rq g) : (ZMod p)ˣ) : ZMod p) • ((d : Dual (ZMod p) B) ∘ₗ B.ρ (rq g)⁻¹)
    = (d : Dual (ZMod p) B) := d.2 g
  refine LinearMap.ext fun a => ?_
  have hψ' : ψ (A.ρ (rq g)⁻¹ a) = B.ρ (rq g)⁻¹ (ψ a) := by rw [← map_inv, hψ, map_inv]
  have := LinearMap.congr_fun h (ψ a)
  simp only [LinearMap.smul_apply, LinearMap.comp_apply] at this ⊢
  rw [hψ']; exact this

def dualPull : (D₁ B q).ρ.invariants →ₗ[ZMod p] (D₁ A q).ρ.invariants where
  toFun d := ⟨(d : Dual (ZMod p) B) ∘ₗ ψ, dualComp_mem q ψ hψ d⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[scoped simp] lemma coe_dualPull (d : (D₁ B q).ρ.invariants) :
    ((dualPull q ψ hψ d : (D₁ A q).ρ.invariants) : Dual (ZMod p) A) = (d : Dual (ZMod p) B) ∘ₗ ψ := rfl

lemma theta2_locPush_apply (inv : continuousH2 rq (Nq p q) →ₗ[ZMod p] ZMod p)
    (θA : continuousH2 rq (Rep.res rq A) →ₗ[ZMod p] Dual (ZMod p) (D₁ A q).ρ.invariants)
    (hθA : IsTheta2 rq (Module.Dual.eval (ZMod p) A : Rep.res rq A →ₗ[ZMod p] D₁ A q →ₗ[ZMod p] Nq p q) inv θA)
    (θB : continuousH2 rq (Rep.res rq B) →ₗ[ZMod p] Dual (ZMod p) (D₁ B q).ρ.invariants)
    (hθB : IsTheta2 rq (Module.Dual.eval (ZMod p) B : Rep.res rq B →ₗ[ZMod p] D₁ B q →ₗ[ZMod p] Nq p q) inv θB)
    (y : continuousH2 rq (Rep.res rq A)) (d : (D₁ B q).ρ.invariants) :
    θB (locPush ψ hψ rq y) d = θA y (dualPull q ψ hψ d) := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  change θB (continuousH2π rq _ (levelCocycles₂Map _ _ _ _ c)) d = θA (continuousH2π rq _ c) _
  rw [theta2_mk_apply B q inv θB hθB, theta2_mk_apply A q inv θA hθA]
  congr 2

end Local

section RightExact

variable {p : ℕ} [Fact p.Prime] (q : Nat.Primes)
  {A B : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)}
  (ψ : A →ₗ[ZMod p] B) (hψ : ∀ (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (a : A), ψ (A.ρ g a) = B.ρ g (ψ a))

local notation "rq" => primeLocalToGlobal q
local notation "Gq" => primeLocalGaloisGroup q

abbrev toTop : Gq →* ↥(⊤ : Subgroup Gq) := (Subgroup.topEquiv : ↥(⊤ : Subgroup Gq) ≃* Gq).symm.toMonoidHom

abbrev rTop : ↥(⊤ : Subgroup Gq) →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :=
  (primeLocalToGlobal q).comp (⊤ : Subgroup Gq).subtype

abbrev resTop (X : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) : Rep (ZMod p) ↥(⊤ : Subgroup Gq) :=
  Rep.res (⊤ : Subgroup Gq).subtype (Rep.res rq X)

def fwdTop (X : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) :
    continuousH2 rq (Rep.res rq X) →ₗ[ZMod p] continuousH2 (rTop q) (resTop q X) :=
  continuousH2Map (rH := rq) (rG := rTop q) (⊤ : Subgroup Gq).subtype (fun _ => rfl)
    (LinearMap.id : Rep.res rq X →ₗ[ZMod p] resTop q X) (fun _ _ => rfl)

def bwdTop (X : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) :
    continuousH2 (rTop q) (resTop q X) →ₗ[ZMod p] continuousH2 rq (Rep.res rq X) :=
  continuousH2Map (rH := rTop q) (rG := rq) (toTop q) (fun _ => rfl)
    (LinearMap.id : resTop q X →ₗ[ZMod p] Rep.res rq X) (fun _ _ => rfl)

lemma bwdTop_fwdTop (X : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (y : continuousH2 rq (Rep.res rq X)) : bwdTop q X (fwdTop q X y) = y := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rfl

def homTop : resTop q A ⟶ resTop q B :=
  Rep.ofHom ((ψ : resTop q A →ₗ[ZMod p] resTop q B).intertwiningMap_of_isIntertwiningMap
    (resTop q A).ρ (resTop q B).ρ (fun g a => hψ (rq g.1) a))

lemma bwdTop_mapHom (y : continuousH2 (rTop q) (resTop q A)) :
    bwdTop q B (continuousH2MapHom (rTop q) (homTop q ψ hψ) y) = locPush ψ hψ rq (bwdTop q A y) := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rfl

include hψ in

theorem locPush_surjective [FiniteDimensional (ZMod p) A]
    (hsmA : ∀ a : A, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s ∈ F.fixingSubgroup, A.ρ s a = a)
    (hψs : Function.Surjective ψ) :
    Function.Surjective (locPush ψ hψ rq) := by
  intro y
  have hS : ∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧
      F₀.fixingSubgroup.comap (primeLocalToGlobal q) ≤ (⊤ : Subgroup Gq) := ⟨⊥, inferInstance, le_top⟩
  have hsm' : ∀ b : resTop q A, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s : ↥(⊤ : Subgroup Gq), ((primeLocalToGlobal q).comp (⊤ : Subgroup Gq).subtype) s ∈ F.fixingSubgroup →
        (resTop q A).ρ s b = b := fun b =>
    let ⟨F, hF, h⟩ := hsmA b; ⟨F, hF, fun s hs => h _ hs⟩
  haveI : FiniteDimensional (ZMod p) (resTop q A) := ‹FiniteDimensional (ZMod p) A›
  have hsurj := continuousH2MapHom_surjective_of_surjective_of_primeLocal (p := p) q (⊤ : Subgroup Gq) hS
    (homTop q ψ hψ) hsm' hψs
  obtain ⟨x', hx'⟩ := hsurj (fwdTop q B y)
  refine ⟨bwdTop q A x', ?_⟩
  rw [← bwdTop_mapHom, hx', bwdTop_fwdTop]

end RightExact

section Global

variable {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes)
  (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))

abbrev NQ (p : ℕ) [Fact p.Prime] : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :=
  ofChar (k := ZMod p) (cycloChar p)

lemma apply_ρ_of_mem_invariants_global (d : (M.dualTwist (cycloChar p)).ρ.invariants)
    (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (m : M) :
    (d : Dual (ZMod p) M) (M.ρ g m) = ((cycloChar p g : (ZMod p)ˣ) : ZMod p) * (d : Dual (ZMod p) M) m := by
  have h' := congrArg (fun f : Dual (ZMod p) M => f (M.ρ g m)) (d.2 g)
  simp only at h'
  rw [← h']
  simp [Representation.twist_apply_apply, Module.Dual.transpose_apply, Representation.inv_self_apply]

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

@[scoped simp] lemma ιqLin_apply (d : (M.dualTwist (cycloChar p)).ρ.invariants) : ιqLin S M q d = ιq S M q d := rfl

lemma ιqLin_injective : Function.Injective (ιqLin S M q) := by
  intro d d' h
  apply Subtype.ext
  exact congrArg (fun x : (D₁ M (q : Nat.Primes)).ρ.invariants => (x : Dual (ZMod p) M)) h

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
  exact theta2_mk_apply M (q : Nat.Primes) (localInv p ζ (q : Nat.Primes)) θ hθ
    (levelCocycles₂Map (rH := MonoidHom.id _) (rG := extArithLoc S (Sum.inr q))
      (extArithLoc S (Sum.inr q)) (fun _ => rfl)
      (LinearMap.id : M →ₗ[ZMod p] Rep.res (extArithLoc S (Sum.inr q)) M) (fun _ _ => rfl)
      (levelCocyclesS₂ToLevelCocycles₂ S M c)) (ιq S M q d)

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

abbrev kerInf : Submodule (ZMod p) (continuousH2S S M) :=
  LinearMap.ker (locRes₂S S M (extArithLoc S (Sum.inl ())))

def rangeRes : Submodule (ZMod p) (LocProd S M) := (kerInf S M).map (locPi S M)

def projq : LocProd S M →ₗ[ZMod p]
    continuousH2 (extArithLoc S (Sum.inr q)) (Rep.res (extArithLoc S (Sum.inr q)) M) where
  toFun z := z q
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[scoped simp] lemma projq_apply (z : LocProd S M) : projq S M q z = z q := rfl

variable
  (θ₂ : ∀ q : ↥S,
      continuousH2 (extArithLoc S (Sum.inr q)) (Rep.res (extArithLoc S (Sum.inr q)) M) →ₗ[ZMod p]
        Module.Dual (ZMod p) (Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p))).ρ.invariants)

def Lam : LocProd S M →ₗ[ZMod p] Module.Dual (ZMod p) (M.dualTwist (cycloChar p)).ρ.invariants :=
  ∑ q : ↥S, (ιqLin S M q).dualMap ∘ₗ θ₂ q ∘ₗ projq S M q

lemma Lam_apply (z : LocProd S M) (d : (M.dualTwist (cycloChar p)).ρ.invariants) :
    Lam S M θ₂ z d = ∑ q : ↥S, θ₂ q (z q) (ιq S M q d) := by
  simp only [Lam, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.dualMap_apply]
  rfl

variable (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p)
  (hθ₂ : ∀ q : ↥S,
      haveI : Fact (((q : Nat.Primes) : ℕ)).Prime := ⟨(q : Nat.Primes).prop⟩
      IsTheta2 (extArithLoc S (Sum.inr q))
        (Module.Dual.eval (ZMod p) M :
          Rep.res (extArithLoc S (Sum.inr q)) M →ₗ[ZMod p]
            Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p)) →ₗ[ZMod p]
              ofChar (k := ZMod p) ((cycloChar p).comp (extArithLoc S (Sum.inr q))))
        (localInv p ζ (q : Nat.Primes)) (θ₂ q))
  (hp2 : p ≠ 2)

include hζ hθ₂ hp2 in

lemma Lam_locPi_eq_zero (x : continuousH2S S M) (hx : x ∈ kerInf S M) : Lam S M θ₂ (locPi S M x) = 0 := by
  refine LinearMap.ext fun d => ?_
  rw [Lam_apply, LinearMap.zero_apply]
  have hc : locRes₂S S (NQ p) (extArithLoc S (Sum.inl ())) (dStar S M d x) = 0 := by
    rw [dStar, locRes₂S_continuousH2SMap, LinearMap.mem_ker.1 hx, map_zero]
  have hrecip := sum_localInv_locRes2S_eq_zero_of_ne_two S hp2 ζ hζ (dStar S M d x) hc
  refine Eq.trans (Finset.sum_congr rfl fun q _ => ?_) hrecip
  exact theta2_locRes_apply S M q ζ (θ₂ q) (hθ₂ q) x d

variable (hsm : ∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s ∈ F.fixingSubgroup, M.ρ s m = m)

include hsm hζ hθ₂ in

lemma bijective_theta2_at [FiniteDimensional (ZMod p) M] (q : ↥S) : Function.Bijective (θ₂ q) := by
  haveI : Fact (((q : Nat.Primes) : ℕ)).Prime := ⟨(q : Nat.Primes).prop⟩
  exact bijective_theta2 M hsm (q : Nat.Primes) ζ hζ (θ₂ q) (hθ₂ q)

variable (hpS : pPrime p ∈ S)

include hsm hζ hθ₂ hpS in

lemma Lam_surjective [FiniteDimensional (ZMod p) M] : Function.Surjective (Lam S M θ₂) := by
  classical
  intro φ
  set q₀ : ↥S := ⟨pPrime p, hpS⟩
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (ιqLin S M q₀)
    (LinearMap.ker_eq_bot.2 (ιqLin_injective S M q₀))
  obtain ⟨w, hw⟩ := (bijective_theta2_at S M θ₂ ζ hζ hθ₂ hsm q₀).2 (φ ∘ₗ g)
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

lemma finite_locProd [FiniteDimensional (ZMod p) M] : Module.Finite (ZMod p) (LocProd S M) := by
  have hq : ∀ q : ↥S, Module.Finite (ZMod p)
      (continuousH2 (extArithLoc S (Sum.inr q)) (Rep.res (extArithLoc S (Sum.inr q)) M)) := fun q =>
    Module.Finite.of_injective (θ₂ q) (bijective_theta2_at S M θ₂ ζ hζ hθ₂ hsm q).1
  exact (Module.Finite.pi : Module.Finite (ZMod p)
    (∀ q : ↥S, continuousH2 (extArithLoc S (Sum.inr q)) (Rep.res (extArithLoc S (Sum.inr q)) M)))

include hpS hsm hζ hθ₂ hp2 in

lemma rangeRes_eq_ker_Lam [FiniteDimensional (ZMod p) M]
    (h : ∃ W : Submodule (ZMod p)
        (∀ q : ↥S, continuousH2 (extArithLoc S (Sum.inr q)) (Rep.res (extArithLoc S (Sum.inr q)) M)),
      Module.Finite (ZMod p) W ∧
      Module.finrank (ZMod p) W ≤ Module.finrank (ZMod p) (M.dualTwist (cycloChar p)).ρ.invariants ∧
      (LinearMap.ker (locRes₂S S M (extArithLoc S (Sum.inl ())))).map
          (LinearMap.pi fun q : ↥S => locRes₂S S M (extArithLoc S (Sum.inr q))) ⊔ W = ⊤) :
    rangeRes S M = LinearMap.ker (Lam S M θ₂) := by
  haveI := finite_locProd S M θ₂ ζ hζ hθ₂ hsm
  obtain ⟨W, hWfin, hWle, hWsup⟩ := h
  let W' : Submodule (ZMod p) (LocProd S M) := W
  haveI : Module.Finite (ZMod p) W' := hWfin
  have hWle' : Module.finrank (ZMod p) W' ≤ Module.finrank (ZMod p) (M.dualTwist (cycloChar p)).ρ.invariants :=
    hWle
  have hWsup' : rangeRes S M ⊔ W' = ⊤ := hWsup
  have hle : rangeRes S M ≤ LinearMap.ker (Lam S M θ₂) := by
    rintro _ ⟨x, hx, rfl⟩
    exact Lam_locPi_eq_zero S M θ₂ ζ hζ hθ₂ hp2 x hx
  have hsurj := Lam_surjective S M θ₂ ζ hζ hθ₂ hsm hpS
  have h1 := LinearMap.finrank_range_add_finrank_ker (Lam S M θ₂)
  rw [LinearMap.range_eq_top.2 hsurj, finrank_top] at h1
  have h2 : Module.finrank (ZMod p) (Module.Dual (ZMod p) (M.dualTwist (cycloChar p)).ρ.invariants)
      = Module.finrank (ZMod p) (M.dualTwist (cycloChar p)).ρ.invariants := Subspace.dual_finrank_eq
  have h3 : Module.finrank (ZMod p) (LocProd S M)
      ≤ Module.finrank (ZMod p) (rangeRes S M) + Module.finrank (ZMod p) W' := by
    rw [← finrank_top (R := ZMod p) (M := LocProd S M), ← hWsup']
    exact Submodule.finrank_add_le_finrank_add_finrank _ _
  refine Submodule.eq_of_le_of_finrank_le hle ?_
  omega

include hpS hsm hζ hθ₂ in

lemma exists_supplement_of_ker_Lam_le [FiniteDimensional (ZMod p) M]
    (h : LinearMap.ker (Lam S M θ₂) ≤ rangeRes S M) :
    ∃ W : Submodule (ZMod p)
        (∀ q : ↥S, continuousH2 (extArithLoc S (Sum.inr q)) (Rep.res (extArithLoc S (Sum.inr q)) M)),
      Module.Finite (ZMod p) W ∧
      Module.finrank (ZMod p) W ≤ Module.finrank (ZMod p) (M.dualTwist (cycloChar p)).ρ.invariants ∧
      (LinearMap.ker (locRes₂S S M (extArithLoc S (Sum.inl ())))).map
          (LinearMap.pi fun q : ↥S => locRes₂S S M (extArithLoc S (Sum.inr q))) ⊔ W = ⊤ := by
  haveI := finite_locProd S M θ₂ ζ hζ hθ₂ hsm
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl (LinearMap.ker (Lam S M θ₂))
  have hsurj := Lam_surjective S M θ₂ ζ hζ hθ₂ hsm hpS
  have h1 := LinearMap.finrank_range_add_finrank_ker (Lam S M θ₂)
  rw [LinearMap.range_eq_top.2 hsurj, finrank_top] at h1
  have h2 : Module.finrank (ZMod p) (Module.Dual (ZMod p) (M.dualTwist (cycloChar p)).ρ.invariants)
      = Module.finrank (ZMod p) (M.dualTwist (cycloChar p)).ρ.invariants := Subspace.dual_finrank_eq
  have h3 := Submodule.finrank_add_eq_of_isCompl hW
  have hfin : Module.Finite (ZMod p) (W : Submodule (ZMod p) (LocProd S M)) := inferInstance
  refine ⟨W, hfin, ?_, ?_⟩
  · change Module.finrank (ZMod p) W ≤ _
    omega
  · change rangeRes S M ⊔ W = ⊤
    exact eq_top_iff.2 (hW.sup_eq_top ▸ sup_le_sup_right h W)

end Global

section Natural

variable {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes)
  {A B : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)}
  (ψ : A →ₗ[ZMod p] B) (hψ : ∀ (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (a : A), ψ (A.ρ g a) = B.ρ g (ψ a))

def locPushPi : LocProd S A →ₗ[ZMod p] LocProd S B where
  toFun z := fun q => locPush ψ hψ (extArithLoc S (Sum.inr q)) (z q)
  map_add' z z' := by
    funext q; exact (locPush ψ hψ (extArithLoc S (Sum.inr q))).map_add (z q) (z' q)
  map_smul' c z := by
    funext q; exact (locPush ψ hψ (extArithLoc S (Sum.inr q))).map_smul c (z q)

@[scoped simp] lemma locPushPi_apply (z : LocProd S A) (q : ↥S) :
    locPushPi S ψ hψ z q = locPush ψ hψ (extArithLoc S (Sum.inr q)) (z q) := rfl

lemma locPushPi_locPi (x : continuousH2S S A) :
    locPushPi S ψ hψ (locPi S A x) = locPi S B (continuousH2SMap S ψ hψ x) := by
  funext q
  rw [locPushPi_apply, locPi_apply, locPi_apply, locRes₂S_continuousH2SMap]

include hψ in
lemma dualCompGlob_mem (d : (B.dualTwist (cycloChar p)).ρ.invariants) :
    ((d : Dual (ZMod p) B) ∘ₗ ψ : Dual (ZMod p) A) ∈ (A.dualTwist (cycloChar p)).ρ.invariants := by
  intro g
  change ((cycloChar p g : (ZMod p)ˣ) : ZMod p) • (((d : Dual (ZMod p) B) ∘ₗ ψ) ∘ₗ A.ρ g⁻¹)
    = (d : Dual (ZMod p) B) ∘ₗ ψ
  have h : ((cycloChar p g : (ZMod p)ˣ) : ZMod p) • ((d : Dual (ZMod p) B) ∘ₗ B.ρ g⁻¹)
    = (d : Dual (ZMod p) B) := d.2 g
  refine LinearMap.ext fun a => ?_
  have := LinearMap.congr_fun h (ψ a)
  simp only [LinearMap.smul_apply, LinearMap.comp_apply] at this ⊢
  rw [hψ]; exact this

def dualPullGlob : (B.dualTwist (cycloChar p)).ρ.invariants →ₗ[ZMod p] (A.dualTwist (cycloChar p)).ρ.invariants where
  toFun d := ⟨(d : Dual (ZMod p) B) ∘ₗ ψ, dualCompGlob_mem ψ hψ d⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma ιq_dualPullGlob (q : ↥S) (d : (B.dualTwist (cycloChar p)).ρ.invariants) :
    ιq S A q (dualPullGlob ψ hψ d) = dualPull (q : Nat.Primes) ψ hψ (ιq S B q d) := rfl

variable
  (θA : ∀ q : ↥S,
      continuousH2 (extArithLoc S (Sum.inr q)) (Rep.res (extArithLoc S (Sum.inr q)) A) →ₗ[ZMod p]
        Module.Dual (ZMod p) (Rep.res (extArithLoc S (Sum.inr q)) (A.dualTwist (cycloChar p))).ρ.invariants)
  (θB : ∀ q : ↥S,
      continuousH2 (extArithLoc S (Sum.inr q)) (Rep.res (extArithLoc S (Sum.inr q)) B) →ₗ[ZMod p]
        Module.Dual (ZMod p) (Rep.res (extArithLoc S (Sum.inr q)) (B.dualTwist (cycloChar p))).ρ.invariants)
  (ζ : AlgebraicClosure ℚ)
  (hθA : ∀ q : ↥S,
      haveI : Fact (((q : Nat.Primes) : ℕ)).Prime := ⟨(q : Nat.Primes).prop⟩
      IsTheta2 (extArithLoc S (Sum.inr q))
        (Module.Dual.eval (ZMod p) A :
          Rep.res (extArithLoc S (Sum.inr q)) A →ₗ[ZMod p]
            Rep.res (extArithLoc S (Sum.inr q)) (A.dualTwist (cycloChar p)) →ₗ[ZMod p]
              ofChar (k := ZMod p) ((cycloChar p).comp (extArithLoc S (Sum.inr q))))
        (localInv p ζ (q : Nat.Primes)) (θA q))
  (hθB : ∀ q : ↥S,
      haveI : Fact (((q : Nat.Primes) : ℕ)).Prime := ⟨(q : Nat.Primes).prop⟩
      IsTheta2 (extArithLoc S (Sum.inr q))
        (Module.Dual.eval (ZMod p) B :
          Rep.res (extArithLoc S (Sum.inr q)) B →ₗ[ZMod p]
            Rep.res (extArithLoc S (Sum.inr q)) (B.dualTwist (cycloChar p)) →ₗ[ZMod p]
              ofChar (k := ZMod p) ((cycloChar p).comp (extArithLoc S (Sum.inr q))))
        (localInv p ζ (q : Nat.Primes)) (θB q))

include hθA hθB in

lemma thetaB_locPush (q : ↥S) (y : continuousH2 (extArithLoc S (Sum.inr q)) (Rep.res (extArithLoc S (Sum.inr q)) A))
    (d : (D₁ B (q : Nat.Primes)).ρ.invariants) :
    θB q (locPush ψ hψ (extArithLoc S (Sum.inr q)) y) d = θA q y (dualPull (q : Nat.Primes) ψ hψ d) := by
  haveI : Fact (((q : Nat.Primes) : ℕ)).Prime := ⟨(q : Nat.Primes).prop⟩
  exact theta2_locPush_apply (q : Nat.Primes) ψ hψ (localInv p ζ (q : Nat.Primes)) (θA q) (hθA q) (θB q) (hθB q) y d

include hθA hθB in

lemma Lam_locPushPi (z : LocProd S A) (d : (B.dualTwist (cycloChar p)).ρ.invariants) :
    Lam S B θB (locPushPi S ψ hψ z) d = Lam S A θA z (dualPullGlob ψ hψ d) := by
  rw [Lam_apply, Lam_apply]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [locPushPi_apply, ιq_dualPullGlob]
  exact thetaB_locPush S ψ hψ θA θB ζ hθA hθB q (z q) (ιq S B q d)

end Natural

section Descent

variable {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
  (M₁ M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
  [FiniteDimensional (ZMod p) M₁] [FiniteDimensional (ZMod p) M]
  (hsm₁ : ∀ m : M₁, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s ∈ F.fixingSubgroup, M₁.ρ s m = m)
  (π : M₁ →ₗ[ZMod p] M) (hπ : ∀ (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (m : M₁), π (M₁.ρ g m) = M.ρ g (π m))
  (hπs : Function.Surjective π)

include hsm₁ hπ hπs in
omit [FiniteDimensional (ZMod p) M₁] [FiniteDimensional (ZMod p) M] in

lemma hsm_of_surjective : ∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
    ∀ s ∈ F.fixingSubgroup, M.ρ s m = m := by
  intro m
  obtain ⟨m₁, rfl⟩ := hπs m
  obtain ⟨F, hF, h⟩ := hsm₁ m₁
  exact ⟨F, hF, fun s hs => by rw [← hπ, h s hs]⟩

variable
  (θ₁ : ∀ q : ↥S,
      continuousH2 (extArithLoc S (Sum.inr q)) (Rep.res (extArithLoc S (Sum.inr q)) M₁) →ₗ[ZMod p]
        Module.Dual (ZMod p) (Rep.res (extArithLoc S (Sum.inr q)) (M₁.dualTwist (cycloChar p))).ρ.invariants)
  (θ : ∀ q : ↥S,
      continuousH2 (extArithLoc S (Sum.inr q)) (Rep.res (extArithLoc S (Sum.inr q)) M) →ₗ[ZMod p]
        Module.Dual (ZMod p) (Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p))).ρ.invariants)
  (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p)
  (hθ₁ : ∀ q : ↥S,
      haveI : Fact (((q : Nat.Primes) : ℕ)).Prime := ⟨(q : Nat.Primes).prop⟩
      IsTheta2 (extArithLoc S (Sum.inr q))
        (Module.Dual.eval (ZMod p) M₁ :
          Rep.res (extArithLoc S (Sum.inr q)) M₁ →ₗ[ZMod p]
            Rep.res (extArithLoc S (Sum.inr q)) (M₁.dualTwist (cycloChar p)) →ₗ[ZMod p]
              ofChar (k := ZMod p) ((cycloChar p).comp (extArithLoc S (Sum.inr q))))
        (localInv p ζ (q : Nat.Primes)) (θ₁ q))
  (hθ : ∀ q : ↥S,
      haveI : Fact (((q : Nat.Primes) : ℕ)).Prime := ⟨(q : Nat.Primes).prop⟩
      IsTheta2 (extArithLoc S (Sum.inr q))
        (Module.Dual.eval (ZMod p) M :
          Rep.res (extArithLoc S (Sum.inr q)) M →ₗ[ZMod p]
            Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p)) →ₗ[ZMod p]
              ofChar (k := ZMod p) ((cycloChar p).comp (extArithLoc S (Sum.inr q))))
        (localInv p ζ (q : Nat.Primes)) (θ q))

include hpS hsm₁ hπs hζ hθ₁ hθ in

lemma exists_correction (Φ : Module.Dual (ZMod p) (M₁.dualTwist (cycloChar p)).ρ.invariants)
    (hΦ : ∀ d₁ : (M₁.dualTwist (cycloChar p)).ρ.invariants,
      (∃ e : Dual (ZMod p) M, (d₁ : Dual (ZMod p) M₁) = e ∘ₗ π) → Φ d₁ = 0) :
    ∃ w : continuousH2 (extArithLoc S (Sum.inr ⟨pPrime p, hpS⟩)) (Rep.res (extArithLoc S (Sum.inr ⟨pPrime p, hpS⟩)) M₁),
      locPush π hπ (extArithLoc S (Sum.inr ⟨pPrime p, hpS⟩)) w = 0 ∧
      ∀ d₁ : (M₁.dualTwist (cycloChar p)).ρ.invariants, θ₁ ⟨pPrime p, hpS⟩ w (ιq S M₁ ⟨pPrime p, hpS⟩ d₁) = Φ d₁ := by
  classical
  set q₀ : ↥S := ⟨pPrime p, hpS⟩
  haveI : Fact (((q₀ : Nat.Primes) : ℕ)).Prime := ⟨(q₀ : Nat.Primes).prop⟩

  let Aloc := (D₁ M₁ (q₀ : Nat.Primes)).ρ.invariants
  let C : Submodule (ZMod p) Aloc := LinearMap.range (dualPull (q₀ : Nat.Primes) π hπ)

  let r : (M₁.dualTwist (cycloChar p)).ρ.invariants →ₗ[ZMod p] Aloc ⧸ C := C.mkQ ∘ₗ ιqLin S M₁ q₀

  have hker : LinearMap.ker r ≤ LinearMap.ker Φ := by
    intro d₁ hd₁
    rw [LinearMap.mem_ker] at hd₁ ⊢
    have hmem : ιq S M₁ q₀ d₁ ∈ C := by
      first | simpa [r, Submodule.Quotient.mk_eq_zero] using hd₁ | (simp [r, Submodule.Quotient.mk_eq_zero] at hd₁; exact hd₁)
    obtain ⟨e, he⟩ := hmem
    refine hΦ d₁ ⟨(e : Dual (ZMod p) M), ?_⟩
    change ((ιq S M₁ q₀ d₁ : Aloc) : Dual (ZMod p) M₁)
      = ((dualPull (q₀ : Nat.Primes) π hπ e : Aloc) : Dual (ZMod p) M₁)
    rw [he]

  obtain ⟨Φ', hΦ'⟩ : ∃ Φ' : Module.Dual (ZMod p) (Aloc ⧸ C), Φ' ∘ₗ r = Φ := by
    let Φr : LinearMap.range r →ₗ[ZMod p] ZMod p :=
      (LinearMap.ker r).liftQ Φ hker ∘ₗ (LinearMap.quotKerEquivRange r).symm.toLinearMap
    obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (LinearMap.range r).subtype
      (by simp)
    refine ⟨Φr ∘ₗ g, LinearMap.ext fun d₁ => ?_⟩
    have hgr : g (r d₁) = ⟨r d₁, LinearMap.mem_range_self r d₁⟩ := by
      have := LinearMap.congr_fun hg ⟨r d₁, LinearMap.mem_range_self r d₁⟩
      simpa using this
    simp only [LinearMap.comp_apply, hgr, Φr, LinearEquiv.coe_coe]
    have : (LinearMap.quotKerEquivRange r).symm ⟨r d₁, LinearMap.mem_range_self r d₁⟩
        = (LinearMap.ker r).mkQ d₁ := by
      rw [LinearEquiv.symm_apply_eq]
      rfl
    rw [this]
    rfl

  obtain ⟨w, hw⟩ := (bijective_theta2_at S M₁ θ₁ ζ hζ hθ₁ hsm₁ q₀).2 (Φ' ∘ₗ C.mkQ)
  refine ⟨w, ?_, fun d₁ => ?_⟩
  ·
    have hsmM := hsm_of_surjective M₁ M hsm₁ π hπ hπs
    apply (bijective_theta2_at S M θ ζ hζ hθ hsmM q₀).1
    rw [map_zero]
    refine LinearMap.ext fun e => ?_
    rw [thetaB_locPush S π hπ θ₁ θ ζ hθ₁ hθ q₀ w e, hw, LinearMap.zero_apply, LinearMap.comp_apply]
    convert (map_zero Φ')
    exact (Submodule.Quotient.mk_eq_zero C).2 (LinearMap.mem_range_self _ e)
  · rw [hw]
    have := LinearMap.congr_fun hΦ' d₁
    exact this

include hpS hsm₁ hπ hπs hζ hθ₁ hθ in

lemma ker_Lam_le_rangeRes (h₁ : LinearMap.ker (Lam S M₁ θ₁) ≤ rangeRes S M₁) :
    LinearMap.ker (Lam S M θ) ≤ rangeRes S M := by
  classical
  intro z hz
  rw [LinearMap.mem_ker] at hz
  set q₀ : ↥S := ⟨pPrime p, hpS⟩

  have hlift : ∀ q : ↥S, ∃ y, locPush π hπ (extArithLoc S (Sum.inr q)) y = z q := fun q => by
    haveI : Fact (((q : Nat.Primes) : ℕ)).Prime := ⟨(q : Nat.Primes).prop⟩
    exact locPush_surjective (q : Nat.Primes) π hπ hsm₁ hπs (z q)
  choose z₁ hz₁ using hlift
  have hz₁' : locPushPi S π hπ (z₁ : LocProd S M₁) = z := funext hz₁

  have hvan : ∀ d₁ : (M₁.dualTwist (cycloChar p)).ρ.invariants,
      (∃ e : Dual (ZMod p) M, (d₁ : Dual (ZMod p) M₁) = e ∘ₗ π) → Lam S M₁ θ₁ z₁ d₁ = 0 := by
    rintro d₁ ⟨e, he⟩

    have hemem : e ∈ (M.dualTwist (cycloChar p)).ρ.invariants := by
      intro g
      have hd := d₁.2 g
      change ((cycloChar p g : (ZMod p)ˣ) : ZMod p) • ((d₁ : Dual (ZMod p) M₁) ∘ₗ M₁.ρ g⁻¹)
        = (d₁ : Dual (ZMod p) M₁) at hd
      change ((cycloChar p g : (ZMod p)ˣ) : ZMod p) • (e ∘ₗ M.ρ g⁻¹) = e
      refine LinearMap.ext fun m => ?_
      obtain ⟨m₁, rfl⟩ := hπs m
      have := LinearMap.congr_fun hd m₁
      rw [he] at this
      simp only [LinearMap.smul_apply, LinearMap.comp_apply] at this ⊢
      rw [← hπ]; exact this
    have hd₁ : d₁ = dualPullGlob π hπ ⟨e, hemem⟩ := Subtype.ext he
    rw [hd₁, ← Lam_locPushPi S π hπ θ₁ θ ζ hθ₁ hθ, hz₁', hz, LinearMap.zero_apply]

  obtain ⟨w, hw0, hw⟩ := exists_correction S hpS M₁ M hsm₁ π hπ hπs θ₁ θ ζ hζ hθ₁ hθ (Lam S M₁ θ₁ z₁) hvan
  set z₁' : LocProd S M₁ := (z₁ : LocProd S M₁) - (Pi.single q₀ w : LocProd S M₁)
  have hz₁'ker : z₁' ∈ LinearMap.ker (Lam S M₁ θ₁) := by
    rw [LinearMap.mem_ker]
    refine LinearMap.ext fun d₁ => ?_
    rw [Lam_apply, LinearMap.zero_apply]
    have hq : ∀ q : ↥S, θ₁ q (z₁' q) (ιq S M₁ q d₁)
        = θ₁ q (z₁ q) (ιq S M₁ q d₁) - θ₁ q ((Pi.single q₀ w : LocProd S M₁) q) (ιq S M₁ q d₁) := fun q => by
      change θ₁ q (z₁ q - (Pi.single q₀ w : LocProd S M₁) q) _ = _
      rw [map_sub, LinearMap.sub_apply]
    have h1 : ∑ q : ↥S, θ₁ q (z₁ q) (ιq S M₁ q d₁) = Lam S M₁ θ₁ z₁ d₁ := (Lam_apply S M₁ θ₁ z₁ d₁).symm
    have h2 : ∑ q : ↥S, θ₁ q ((Pi.single q₀ w : LocProd S M₁) q) (ιq S M₁ q d₁) = Lam S M₁ θ₁ z₁ d₁ := by
      rw [Finset.sum_eq_single q₀]
      · rw [Pi.single_eq_same, hw]
      · intro q _ hq
        rw [Pi.single_eq_of_ne hq, map_zero, LinearMap.zero_apply]
      · intro h; exact absurd (Finset.mem_univ q₀) h
    rw [Finset.sum_congr rfl fun q _ => hq q, Finset.sum_sub_distrib, h1, h2, sub_self]

  obtain ⟨x₁, hx₁, hx₁z⟩ := h₁ hz₁'ker
  refine ⟨continuousH2SMap S π hπ x₁, ?_, ?_⟩
  · change locRes₂S S M (extArithLoc S (Sum.inl ())) (continuousH2SMap S π hπ x₁) = 0
    rw [locRes₂S_continuousH2SMap, LinearMap.mem_ker.1 hx₁, map_zero]
  · rw [← locPushPi_locPi, hx₁z]
    funext q
    rw [locPushPi_apply]
    change locPush π hπ (extArithLoc S (Sum.inr q)) (z₁ q - (Pi.single q₀ w : LocProd S M₁) q) = z q
    rw [map_sub, hz₁]
    by_cases hq : q = q₀
    · subst hq; rw [Pi.single_eq_same, hw0, sub_zero]
    · rw [Pi.single_eq_of_ne hq, map_zero, sub_zero]

end Descent

end P2M71fOdd
p2m_reactivate "P2MW.S_groupCohomology_exists_range_locRes_continuousH2S_sup_eq_top_of_surjective_of_ne_two.P2M71fOdd"

theorem solution
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hp2 : p ≠ 2) (hpS : pPrime p ∈ S)
    (M₁ M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    [FiniteDimensional (ZMod p) M₁] [FiniteDimensional (ZMod p) M]
    (hsm₁ : ∀ m : M₁, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s ∈ F.fixingSubgroup, M₁.ρ s m = m)
    (π : M₁ →ₗ[ZMod p] M) (hπ : ∀ (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (m : M₁), π (M₁.ρ g m) = M.ρ g (π m))
    (hπs : Function.Surjective π)
    (h₁ : ∃ W₁ : Submodule (ZMod p)
        (∀ q : ↥S, continuousH2 (extArithLoc S (Sum.inr q)) (Rep.res (extArithLoc S (Sum.inr q)) M₁)),
      Module.Finite (ZMod p) W₁ ∧
      Module.finrank (ZMod p) W₁ ≤ Module.finrank (ZMod p) (M₁.dualTwist (cycloChar p)).ρ.invariants ∧
      (LinearMap.ker (locRes₂S S M₁ (extArithLoc S (Sum.inl ())))).map
          (LinearMap.pi fun q : ↥S => locRes₂S S M₁ (extArithLoc S (Sum.inr q))) ⊔ W₁ = ⊤) :
    ∃ W : Submodule (ZMod p)
        (∀ q : ↥S, continuousH2 (extArithLoc S (Sum.inr q)) (Rep.res (extArithLoc S (Sum.inr q)) M)),
      Module.Finite (ZMod p) W ∧
      Module.finrank (ZMod p) W ≤ Module.finrank (ZMod p) (M.dualTwist (cycloChar p)).ρ.invariants ∧
      (LinearMap.ker (locRes₂S S M (extArithLoc S (Sum.inl ())))).map
          (LinearMap.pi fun q : ↥S => locRes₂S S M (extArithLoc S (Sum.inr q))) ⊔ W = ⊤ := by
  classical

  haveI : NeZero ((p : ℕ) : AlgebraicClosure ℚ) := NeZero.charZero
  obtain ⟨ζ, hζ⟩ : ∃ ζ : AlgebraicClosure ℚ, IsPrimitiveRoot ζ p := HasEnoughRootsOfUnity.prim
  have hex₁ := fun q : ↥S =>
    (haveI : Fact (((q : Nat.Primes) : ℕ)).Prime := ⟨(q : Nat.Primes).prop⟩
     P2M71fOdd.exists_theta2 M₁ (q : Nat.Primes) (localInv p ζ (q : Nat.Primes)))
  choose θ₁ hθ₁ using hex₁
  have hex := fun q : ↥S =>
    (haveI : Fact (((q : Nat.Primes) : ℕ)).Prime := ⟨(q : Nat.Primes).prop⟩
     P2M71fOdd.exists_theta2 M (q : Nat.Primes) (localInv p ζ (q : Nat.Primes)))
  choose θ hθ using hex
  have hsm := P2M71fOdd.hsm_of_surjective M₁ M hsm₁ π hπ hπs

  have hker₁ := P2M71fOdd.rangeRes_eq_ker_Lam S M₁ θ₁ ζ hζ hθ₁ hp2 hsm₁ hpS h₁
  have hle := P2M71fOdd.ker_Lam_le_rangeRes S hpS M₁ M hsm₁ π hπ hπs θ₁ θ ζ hζ hθ₁ hθ hker₁.symm.le
  exact P2M71fOdd.exists_supplement_of_ker_Lam_le S M θ ζ hζ hθ hsm hpS hle

end
end S_groupCohomology_exists_range_locRes_continuousH2S_sup_eq_top_of_surjective_of_ne_two
end P2MW
export P2MW.S_groupCohomology_exists_range_locRes_continuousH2S_sup_eq_top_of_surjective_of_ne_two (solution)
