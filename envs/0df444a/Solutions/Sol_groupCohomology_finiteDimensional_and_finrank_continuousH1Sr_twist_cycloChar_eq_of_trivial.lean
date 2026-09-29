-- Prove2me | solution 1 for groupCohomology.finiteDimensional_and_finrank_continuousH1Sr_twist_cycloChar_eq_of_trivial
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/8a747371-b9cc-56b9-9178-88290dbac668

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Theorems.Thm_Rep_nonempty_twist_iso_trivial_twist_tensor
import Theorems.Thm_groupCohomology_finiteDimensional_and_finrank_continuousH1Sr_twist_eq_unitsModP_add_sClassTorsionP
import Theorems.Thm_groupCohomology_finiteDimensional_and_finrank_continuousH2Sr_twist_add_eq_sClassTorsionP_add_sum_placesRep
import Theorems.Thm_NumberField_LevelArith_finrank_invariants_unitsModP_tensor_add_finrank_invariants_eq
import Theorems.Thm_NumberField_LevelArith_normal_levelField_of_isNormalLevel
import Theorems.Thm_groupCohomology_finrank_invariants_archimedean_coind
import Definitions.Def_P2M_Util
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_finiteDimensional_and_finrank_continuousH1Sr_twist_cycloChar_eq_of_trivial
p2m_attr_erase "instance" "NumberField.LevelArith.instCommGroupUnitsModPow groupCohomology.Kummer.instMulDistribMulActionRootsOfUnity M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete groupCohomology.normal_comap_fixingSubgroup groupCohomology.finiteIndex_comap_fixingSubgroup AlgebraicClosure.Rat.isGalois FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions"
p2m_attr_erase "instance" "instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap NumberField.AdelicHaar.locallyCompactSpace_adeleRing NumberField.AdelicHaar.finite_residueField_adicCompletionIntegers NumberField.AdelicHaar.locallyCompactSpace_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_finiteAdeleRing NumberField.AdelicHaar.compactSpace_adicCompletionIntegers NumberField.AdelicHaar.t2Space_finiteAdeleRing NumberField.AdelicHaar.t2Space_matrix_adeleRing NumberField.AdelicHaar.t2Space_adeleRing NumberField.AdelicHaar.fact_isOpen_adicCompletionIntegers NumberField.AdelicHaar.t2Space_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_matrix_adeleRing NumberField.AdelicHaar.t2Space_infiniteAdeleRing NumberField.AdelicHaar.properSpace_adicCompletion ExtCitation.levelSubgroup_normal"
p2m_attr_erase "instance" "ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite Deep.NTSupply.instNormalRayClassSubgroup instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal"
p2m_attr_erase "simp" "NumberField.LevelArith.smul_mk NumberField.LevelArith.selmerRepInt_ρ_apply NumberField.LevelArith.selmerRepField_ρ_apply NumberField.LevelArith.unitsModPowMap_mk groupCohomology.Kummer.coe_kummerCocycleRoots groupCohomology.Kummer.mem_powerSubgroup_iff groupCohomology.Kummer.val_smul_units groupCohomology.Kummer.kummerHom_apply groupCohomology.Kummer.coe_smul_rootsOfUnity Rep.quotientRightTranslation_hom_single Rep.quotientRightTranslationTwist_hom_apply M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk M4aHerbrand.IdeleGaloisDescent.classAct_mk M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq ExtCitation.LocalLevel.coe_smul_OO WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply groupCohomology.continuousH2Inflation_H2π groupCohomology.levelInflate₂_apply groupCohomology.coe_levelInflateCocycles₂ groupCohomology.levelInflate₁_apply M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply"
p2m_attr_erase "simp" "Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul"
p2m_attr_erase "simp" "IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply"
p2m_attr_erase "simp" "NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl IsLocalRing.principalUnits_zero groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply M4aHerbrand.Bridge.finiteConorm_apply M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec"
p2m_attr_erase "simp" "AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Module groupCohomology ExtCitation"
open scoped Classical

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 1600000
set_option Elab.async false

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Module groupCohomology ExtCitation NumberField.LevelArith"
open scoped Classical NumberField.LevelArith Pointwise

namespace TateK

local notation "Γ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

section EqFun
variable {k : Type} [CommRing k] {H : Type} [Group H] (Z : Type) [MulAction H Z] (N : Rep.{0} k H)

def eqFun : Submodule k (Z → N) where
  carrier := {F | ∀ (h : H) (z : Z), F (h • z) = N.ρ h (F z)}
  add_mem' {F G} hF hG := fun h z => by
    show F (h • z) + G (h • z) = N.ρ h (F z + G z)
    rw [hF h z, hG h z, map_add]
  zero_mem' := fun h z => by
    show (0 : N) = N.ρ h 0
    rw [map_zero]
  smul_mem' c F hF := fun h z => by
    show c • F (h • z) = N.ρ h (c • F z)
    rw [hF h z, map_smul]

variable {Z N}
lemma mem_eqFun (F : Z → N) : F ∈ eqFun Z N ↔ ∀ (h : H) (z : Z), F (h • z) = N.ρ h (F z) := Iff.rfl

end EqFun

section A
variable {k : Type} [CommRing k] {H : Type} [Group H] (Z : Type) [MulAction H Z] [Finite Z] (N : Rep.{0} k H)

noncomputable def E : ((Rep.ofMulActionFinsupp k H Z ⊗ N : Rep.{0} k H)) ≃ₗ[k] (Z → N) :=
  (TensorProduct.finsuppScalarLeft k N Z).trans (Finsupp.linearEquivFunOnFinite k N Z)

lemma E_tmul (f : Z →₀ k) (n : N) (z : Z) : E Z N (f ⊗ₜ[k] n) z = f z • n := by
  simp [E, TensorProduct.finsuppScalarLeft_apply_tmul_apply]

lemma E_ρ (h : H) (t : (Rep.ofMulActionFinsupp k H Z ⊗ N : Rep.{0} k H)) (z : Z) :
    E Z N ((Rep.ofMulActionFinsupp k H Z ⊗ N : Rep.{0} k H).ρ h t) z = N.ρ h (E Z N t (h⁻¹ • z)) := by
  induction t using TensorProduct.induction_on generalizing z with
  | zero => simp
  | tmul f n =>
    rw [Rep.tensor_ρ, Representation.tprod_apply, TensorProduct.map_tmul, E_tmul]
    change (Representation.ofMulActionFinsupp k H Z h f) z • N.ρ h n = N.ρ h (E Z N (f ⊗ₜ[k] n) (h⁻¹ • z))
    rw [E_tmul, map_smul, Representation.ofMulActionFinsupp_def, Finsupp.lmapDomain_apply]
    conv_lhs => rw [← smul_inv_smul h z, Finsupp.mapDomain_apply (MulAction.injective h)]
  | add x y hx hy =>
    rw [map_add, map_add, Pi.add_apply, hx, hy, ← map_add, map_add (E Z N) x y, Pi.add_apply]

noncomputable def invariantsEquivEqFun :
    (Rep.ofMulActionFinsupp k H Z ⊗ N : Rep.{0} k H).ρ.invariants ≃ₗ[k] eqFun Z N where
  toFun v := ⟨E Z N v.1, fun h z => by
    have hv := (Representation.mem_invariants _ _).1 v.2 h
    conv_lhs => rw [← hv]
    rw [E_ρ, inv_smul_smul]⟩
  invFun F := ⟨(E Z N).symm F.1, by
    rw [Representation.mem_invariants]
    intro h
    apply (E Z N).injective
    funext z
    rw [E_ρ, LinearEquiv.apply_symm_apply]
    have := F.2 h (h⁻¹ • z)
    rw [smul_inv_smul] at this
    exact this.symm⟩
  map_add' v w := by apply Subtype.ext; exact map_add _ _ _
  map_smul' c v := by apply Subtype.ext; exact map_smul _ _ _
  left_inv v := by apply Subtype.ext; exact (E Z N).symm_apply_apply _
  right_inv F := by apply Subtype.ext; exact (E Z N).apply_symm_apply _

end A

section B
variable (K L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLK : L.fixingSubgroup ≤ K.fixingSubgroup)
  (hnorm : IsNormalLevel K L) (X : Type) [MulAction Γ X]
  {k : Type} [CommRing k] (N : Rep.{0} k ↥K.fixingSubgroup)
  (htriv : ∀ s : ↥K.fixingSubgroup, (s : Γ) ∈ L.fixingSubgroup → N.ρ s = 1)

abbrev Q : Type := MulAction.orbitRel.Quotient ↥L.fixingSubgroup X

noncomputable def pull :
    (letI := orbitQuotientAction K L hnorm X; eqFun (Q L X) N) →ₗ[k] eqFun X N :=
  letI := orbitQuotientAction K L hnorm X
  { toFun := fun F => ⟨fun x => F.1 (Quotient.mk'' x), fun h x => F.2 h (Quotient.mk'' x)⟩
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

include hLK htriv in
lemma const_on_orbit (G : eqFun X N) (a b : X) (hab : (MulAction.orbitRel ↥L.fixingSubgroup X) a b) :
    G.1 a = G.1 b := by
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hab
  obtain ⟨s, rfl⟩ := hab
  have := G.2 ⟨(s : Γ), hLK s.2⟩ b
  rw [htriv ⟨(s : Γ), hLK s.2⟩ s.2] at this
  exact this

noncomputable def push :
    eqFun X N →ₗ[k] (letI := orbitQuotientAction K L hnorm X; eqFun (Q L X) N) :=
  letI := orbitQuotientAction K L hnorm X
  { toFun := fun G => ⟨Quotient.lift G.1 (fun a b hab => const_on_orbit K L hLK X N htriv G a b hab), fun h q => by
      induction q using Quotient.inductionOn with
      | h x => exact G.2 h x⟩
    map_add' := fun _ _ => by apply Subtype.ext; funext q; induction q using Quotient.inductionOn with | h x => rfl
    map_smul' := fun _ _ => by apply Subtype.ext; funext q; induction q using Quotient.inductionOn with | h x => rfl }

noncomputable def eqFunQuotEquiv :
    (letI := orbitQuotientAction K L hnorm X; eqFun (Q L X) N) ≃ₗ[k] eqFun X N :=
  LinearEquiv.ofLinear (pull K L hnorm X N) (push K L hLK hnorm X N htriv)
    (by apply LinearMap.ext; intro G; rfl)
    (by
      apply LinearMap.ext; intro F; apply Subtype.ext; funext q
      induction q using Quotient.inductionOn with
      | h x => rfl)

end B

section C
variable {k : Type} [CommRing k] (H : Subgroup Γ) {D : Type} [Group D] (φ : D →* Γ) (N : Rep.{0} k ↥H)

noncomputable abbrev V := (Rep.res φ (Rep.coind H.subtype N)).ρ.invariants

variable {H φ N}

lemma V_mul_left (f : V H φ N) (h : ↥H) (x : Γ) : f.1.1 ((h : Γ) * x) = N.ρ h (f.1.1 x) := f.1.2 h x

lemma V_mul_right (f : V H φ N) (d : D) (x : Γ) : f.1.1 (x * φ d) = f.1.1 x := by
  have := (Representation.mem_invariants _ _).1 f.2 d
  exact congrFun (congrArg Subtype.val this) x

lemma V_coset (f : V H φ N) {x y : Γ} (hxy : (x : Γ ⧸ φ.range) = (y : Γ ⧸ φ.range)) : f.1.1 x = f.1.1 y := by
  rw [QuotientGroup.eq] at hxy
  obtain ⟨d, hd⟩ := hxy
  have := V_mul_right f d x
  rw [hd, mul_inv_cancel_left] at this
  exact this.symm

variable (H φ N)

noncomputable def toEqFun : V H φ N →ₗ[k] eqFun (Γ ⧸ φ.range) N where
  toFun f := ⟨fun c => f.1.1 c.out, fun h c => by
    show f.1.1 (h • c).out = N.ρ h (f.1.1 c.out)
    rw [← V_mul_left]
    apply V_coset
    rw [QuotientGroup.out_eq']
    show h • c = (((h : Γ) * c.out : Γ) : Γ ⧸ φ.range)
    conv_lhs => rw [← QuotientGroup.out_eq' c]
    rfl⟩
  map_add' f g := rfl
  map_smul' c f := rfl

noncomputable def ofEqFun : eqFun (Γ ⧸ φ.range) N →ₗ[k] V H φ N where
  toFun F := ⟨⟨fun x => F.1 (x : Γ ⧸ φ.range), fun h x => F.2 h (x : Γ ⧸ φ.range)⟩, by
    rw [Representation.mem_invariants]
    intro d
    apply Subtype.ext
    funext x
    show F.1 ((x * φ d : Γ) : Γ ⧸ φ.range) = F.1 (x : Γ ⧸ φ.range)
    rw [QuotientGroup.mk_mul_of_mem x (MonoidHom.mem_range.2 ⟨d, rfl⟩)]⟩
  map_add' F G := rfl
  map_smul' c F := rfl

noncomputable def invariantsCoindEquivEqFun : V H φ N ≃ₗ[k] eqFun (Γ ⧸ φ.range) N :=
  LinearEquiv.ofLinear (toEqFun H φ N) (ofEqFun H φ N)
    (by
      apply LinearMap.ext; intro F; apply Subtype.ext; funext c
      show F.1 ((c.out : Γ) : Γ ⧸ φ.range) = F.1 c
      rw [QuotientGroup.out_eq'])
    (by
      apply LinearMap.ext; intro f; apply Subtype.ext; apply Subtype.ext; funext x
      show f.1.1 ((x : Γ ⧸ φ.range).out) = f.1.1 x
      exact V_coset f (QuotientGroup.out_eq' _))

end C

end TateK

local instance TateK.isAlgebraicQbar : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) :=
  AlgebraicClosure.isAlgebraic ℚ
local instance TateK.isAlgClosureQbar : IsAlgClosure ℚ (AlgebraicClosure ℚ) :=
  ⟨inferInstance, inferInstance⟩
local instance TateK.normalQbar : Normal ℚ (AlgebraicClosure ℚ) :=
  IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)

namespace TateK

local notation "Γ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

section finiteQ
variable (H D : Subgroup Γ)

noncomputable def orbOfRightCoset : Quotient (QuotientGroup.rightRel H) → MulAction.orbitRel.Quotient ↥H (Γ ⧸ D) :=
  Quotient.lift (fun x : Γ => (Quotient.mk'' (x : Γ ⧸ D) : MulAction.orbitRel.Quotient ↥H (Γ ⧸ D))) fun a b hab => by
    have hab' : b * a⁻¹ ∈ H := QuotientGroup.rightRel_apply.1 hab
    apply Quotient.sound
    change (MulAction.orbitRel H (Γ ⧸ D)) (a : Γ ⧸ D) (b : Γ ⧸ D)
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
    refine ⟨⟨a * b⁻¹, by simpa using H.inv_mem hab'⟩, ?_⟩
    change (((a * b⁻¹) * b : Γ) : Γ ⧸ D) = (a : Γ ⧸ D)
    rw [inv_mul_cancel_right]

lemma orbOfRightCoset_surjective : Function.Surjective (orbOfRightCoset H D) := by
  intro q
  induction q using Quotient.inductionOn' with
  | h c =>
    induction c using QuotientGroup.induction_on with
    | H x => exact ⟨Quotient.mk _ x, rfl⟩

lemma finite_orbitQuotient [H.FiniteIndex] : Finite (MulAction.orbitRel.Quotient ↥H (Γ ⧸ D)) := by
  haveI : Finite (Quotient (QuotientGroup.rightRel H)) :=
    Finite.of_equiv _ (QuotientGroup.quotientRightRelEquivQuotientLeftRel H).symm
  exact Finite.of_surjective _ (orbOfRightCoset_surjective H D)

end finiteQ

theorem finiteIndex_fixingSubgroup (E : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ E] :
    E.fixingSubgroup.FiniteIndex :=
  haveI : Finite (Γ ⧸ E.fixingSubgroup) :=
    Subgroup.quotient_finite_of_isOpen _ (IntermediateField.fixingSubgroup_isOpen E)
  Subgroup.finiteIndex_of_finite_quotient

section invIso
variable {k : Type} [CommRing k] {G : Type} [Group G]

noncomputable def invariantsEquiv {A B : Rep.{0} k G} (e : A ≅ B) : A.ρ.invariants ≃ₗ[k] B.ρ.invariants where
  toFun v := ⟨e.hom.hom v.1, fun g => by rw [← Rep.hom_comm_apply, v.2 g]⟩
  invFun w := ⟨e.inv.hom w.1, fun g => by rw [← Rep.hom_comm_apply, w.2 g]⟩
  map_add' v w := by apply Subtype.ext; exact map_add _ _ _
  map_smul' a v := by apply Subtype.ext; exact map_smul _ _ _
  left_inv v := by apply Subtype.ext; simp
  right_inv w := by apply Subtype.ext; simp

lemma finrank_invariants_eq_of_iso {A B : Rep.{0} k G} (e : A ≅ B) :
    Module.finrank k A.ρ.invariants = Module.finrank k B.ρ.invariants :=
  LinearEquiv.finrank_eq (invariantsEquiv e)

end invIso

theorem finrank_invariants_placesRep_inl_tensor
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes)
    (K L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥K] [FiniteDimensional ℚ ↥L] (hKL : K ≤ L)
    (hnorm : IsNormalLevel K L)
    (N : Rep.{0} (ZMod p) ↥K.fixingSubgroup) [FiniteDimensional (ZMod p) N]
    (htriv : ∀ s : ↥K.fixingSubgroup, (s : Γ) ∈ L.fixingSubgroup → N.ρ s = 1) :
    Module.finrank (ZMod p) (placesRep K L hnorm S (Sum.inl ()) p ⊗ N : Rep.{0} (ZMod p) ↥K.fixingSubgroup).ρ.invariants =
      ∑ᶠ v : Quotient (MulAction.orbitRel ↥K.fixingSubgroup (Γ ⧸ (extArithLoc S (Sum.inl ())).range)),
        Module.finrank (ZMod p) (Rep.res (MulAction.stabilizer (↥K.fixingSubgroup) v.out).subtype N).ρ.invariants := by
  haveI : L.fixingSubgroup.FiniteIndex := finiteIndex_fixingSubgroup L
  haveI : Finite (placesAbove L S (Sum.inl ())) := finite_orbitQuotient L.fixingSubgroup _
  letI := orbitQuotientAction K L hnorm (Γ ⧸ (extArithLoc S (Sum.inl ())).range)
  have hLK : L.fixingSubgroup ≤ K.fixingSubgroup := IntermediateField.fixingSubgroup_antitone hKL
  have e1 := @invariantsEquivEqFun (ZMod p) _ ↥K.fixingSubgroup _ (placesAbove L S (Sum.inl ()))
    (orbitQuotientAction K L hnorm _) inferInstance N
  have e2 := eqFunQuotEquiv K L hLK hnorm (Γ ⧸ (extArithLoc S (Sum.inl ())).range) N htriv
  have e3 := (invariantsCoindEquivEqFun K.fixingSubgroup (extArithLoc S (Sum.inl ())) N).symm
  rw [← groupCohomology.finrank_invariants_archimedean_coind S K N]
  exact LinearEquiv.finrank_eq ((e1.trans e2).trans e3)

end TateK

set_option maxHeartbeats 6400000 in
open TateK in
theorem solution
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (K L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hK : K.IsUnramifiedOutside S) (hL : L.IsUnramifiedOutside S)
    (hKL : K ≤ L)
    (hnorm : ∀ g ∈ K.fixingSubgroup, ∀ s ∈ L.fixingSubgroup, g * s * g⁻¹ ∈ L.fixingSubgroup)
    (hcop : (L.fixingSubgroup.relIndex K.fixingSubgroup).Coprime p)
    (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p) (hζL : ζ ∈ L)
    (h4 : p = 2 → ∃ i ∈ L, i ^ 2 = -1)
    (N : Rep.{0} (ZMod p) ↥K.fixingSubgroup) [FiniteDimensional (ZMod p) N]
    (htriv : ∀ s : ↥K.fixingSubgroup, (s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ L.fixingSubgroup → N.ρ s = 1) :
    FiniteDimensional (ZMod p)
        ↥(continuousH1Sr K.fixingSubgroup.subtype S (N.twist ((cycloChar p).comp K.fixingSubgroup.subtype))) ∧
      FiniteDimensional (ZMod p)
        (continuousH2Sr K.fixingSubgroup.subtype S (N.twist ((cycloChar p).comp K.fixingSubgroup.subtype))) ∧
      Module.finrank (ZMod p)
          ↥(continuousH1Sr K.fixingSubgroup.subtype S (N.twist ((cycloChar p).comp K.fixingSubgroup.subtype))) =
        Module.finrank (ZMod p) (N.twist ((cycloChar p).comp K.fixingSubgroup.subtype)).ρ.invariants +
        Module.finrank (ZMod p)
          (continuousH2Sr K.fixingSubgroup.subtype S (N.twist ((cycloChar p).comp K.fixingSubgroup.subtype))) +
        ∑ᶠ v : Quotient (MulAction.orbitRel ↥K.fixingSubgroup
            ((AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ (extArithLoc S (Sum.inl ())).range)),
          Module.finrank (ZMod p) (Rep.res (MulAction.stabilizer (↥K.fixingSubgroup) v.out).subtype N).ρ.invariants := by
  haveI : FiniteDimensional ℚ ↥K := hK.1
  haveI : FiniteDimensional ℚ ↥L := hL.1
  haveI : Normal ↥K ↥(levelField K L hKL) := NumberField.LevelArith.normal_levelField_of_isNormalLevel K L hKL hnorm

  obtain ⟨hfin1, hKum⟩ :=
    groupCohomology.finiteDimensional_and_finrank_continuousH1Sr_twist_eq_unitsModP_add_sClassTorsionP S hpS K L hK hL
      hKL hnorm hcop ζ hζ hζL N htriv
  obtain ⟨hfin2, hBr⟩ :=
    groupCohomology.finiteDimensional_and_finrank_continuousH2Sr_twist_add_eq_sClassTorsionP_add_sum_placesRep S hpS K L hK
      hL hKL hnorm hcop ζ hζ hζL h4 N htriv
  have hHer := NumberField.LevelArith.finrank_invariants_unitsModP_tensor_add_finrank_invariants_eq S hpS K L hK hL hKL
    hnorm hcop ζ hζ hζL h4 N htriv
  obtain ⟨e0⟩ := Rep.nonempty_twist_iso_trivial_twist_tensor N ((cycloChar p).comp K.fixingSubgroup.subtype)
  have h0 := finrank_invariants_eq_of_iso e0

  have hArch := finrank_invariants_placesRep_inl_tensor S K L hKL hnorm N htriv
  refine ⟨hfin1, hfin2, ?_⟩
  omega

end S_groupCohomology_finiteDimensional_and_finrank_continuousH1Sr_twist_cycloChar_eq_of_trivial
end P2MW
export P2MW.S_groupCohomology_finiteDimensional_and_finrank_continuousH1Sr_twist_cycloChar_eq_of_trivial (solution)
