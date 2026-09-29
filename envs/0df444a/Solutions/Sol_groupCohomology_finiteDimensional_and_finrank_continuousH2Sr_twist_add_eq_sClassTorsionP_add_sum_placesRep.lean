-- Prove2me | solution 1 for groupCohomology.finiteDimensional_and_finrank_continuousH2Sr_twist_add_eq_sClassTorsionP_add_sum_placesRep
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/19d9f34e-c165-5fbf-979d-180db2e0e680

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Definitions.Def_NumberField_LevelArithmeticModP
import Theorems.Thm_groupCohomology_nonempty_continuousH2Sr_twist_linearEquiv_invariants_cyclotomicQuotientH2Rep_tensor
import Theorems.Thm_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_finiteDimensional_and_finrank_continuousH2Sr_twist_add_eq_sClassTorsionP_add_sum_placesRep
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
open scoped Classical NumberField.LevelArith TensorProduct

namespace EQBXAux

variable {k : Type} [Field k] {Γ : Type} [Group Γ]

theorem surjective_of_comp_eq_id' {A B : Rep.{0} k Γ} (s : B ⟶ A) (g : A ⟶ B) (h : s ≫ g = 𝟙 B) : Function.Surjective g.hom := by
  intro y
  refine ⟨s.hom y, ?_⟩
  change (s ≫ g).hom y = y
  rw [h]
  rfl

theorem finiteDimensional_of_pi {ι : Type} [Fintype ι] [DecidableEq ι] (F : ι → Rep.{0} k Γ) (C : Rep.{0} k Γ) (e : C ≅ ∏ᶜ F)
    [FiniteDimensional k C] (i : ι) : FiniteDimensional k (F i) := by
  let s : F i ⟶ ∏ᶜ F := Pi.lift (fun j => if h : j = i then eqToHom (congrArg F h.symm) else 0)
  have hs : s ≫ Pi.π F i = 𝟙 (F i) := by
    simp only [s, Pi.lift_π, eqToHom_refl, dite_true]
  haveI : FiniteDimensional k (∏ᶜ F : Rep.{0} k Γ) :=
    Module.Finite.equiv ((forget₂ (Rep.{0} k Γ) (ModuleCat.{0} k)).mapIso e).toLinearEquiv
  exact Module.Finite.of_surjective (Pi.π F i).hom.toLinearMap (surjective_of_comp_eq_id' s (Pi.π F i) hs)

theorem finrank_invariants_trivial_tensor (N : Rep.{0} k Γ) [FiniteDimensional k N] :
    Module.finrank k (Rep.trivial k Γ k ⊗ N : Rep.{0} k Γ).ρ.invariants = Module.finrank k N.ρ.invariants := by

  let l : (Rep.trivial k Γ k ⊗ N : Rep.{0} k Γ) ≃ₗ[k] N := TensorProduct.lid k N
  have hl : ∀ (g : Γ) (x : (Rep.trivial k Γ k ⊗ N : Rep.{0} k Γ)), l ((Rep.trivial k Γ k ⊗ N : Rep.{0} k Γ).ρ g x) = N.ρ g (l x) := by
    intro g x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a n =>
      rw [Rep.tensor_ρ]
      show l (TensorProduct.map ((Rep.trivial k Γ k).ρ g) (N.ρ g) (a ⊗ₜ n)) = N.ρ g (l (a ⊗ₜ n))
      rw [TensorProduct.map_tmul]
      show (TensorProduct.lid k N) (((Rep.trivial k Γ k).ρ g a) ⊗ₜ (N.ρ g n)) = N.ρ g ((TensorProduct.lid k N) (a ⊗ₜ n))
      rw [TensorProduct.lid_tmul, TensorProduct.lid_tmul, Rep.trivial_ρ_apply, map_smul]
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  let l' : (Rep.trivial k Γ k ⊗ N : Rep.{0} k Γ).ρ.invariants ≃ₗ[k] N.ρ.invariants :=
    { toFun := fun x => ⟨l x.1, fun g => by rw [← hl, x.2 g]⟩
      invFun := fun y => ⟨l.symm y.1, fun g => by
        apply l.injective
        rw [hl, LinearEquiv.apply_symm_apply, y.2 g]⟩
      map_add' := fun x y => Subtype.ext (map_add l x.1 y.1)
      map_smul' := fun c x => Subtype.ext (map_smul l c x.1)
      left_inv := fun x => Subtype.ext (l.symm_apply_apply x.1)
      right_inv := fun y => Subtype.ext (l.apply_symm_apply y.1) }
  exact l'.finrank_eq

theorem finrank_invariants_tensor_of_iso_pi {ι : Type} [Fintype ι] [DecidableEq ι]
    (N C : Rep.{0} k Γ) (F : ι → Rep.{0} k Γ) (e : C ≅ ∏ᶜ F) [∀ i, FiniteDimensional k (F i)] [FiniteDimensional k N] :
    Module.finrank k (C ⊗ N : Rep.{0} k Γ).ρ.invariants = ∑ i, Module.finrank k (F i ⊗ N : Rep.{0} k Γ).ρ.invariants := by
  haveI : ∀ i, FiniteDimensional k (F i ⊗ N : Rep.{0} k Γ) := fun i => inferInstanceAs (Module.Finite k (TensorProduct k (F i) N))

  let T : Rep.{0} k Γ ⥤ Rep.{0} k Γ := tensorRight N
  let I : Rep.{0} k Γ ⥤ ModuleCat k := Rep.invariantsFunctor k Γ
  let e₁ : (C ⊗ N : Rep.{0} k Γ) ≅ ∏ᶜ (fun i => (F i ⊗ N : Rep.{0} k Γ)) := T.mapIso e ≪≫ PreservesProduct.iso T F
  let e₂ : I.obj (C ⊗ N) ≅ ModuleCat.of k ((i : ι) → ↑(I.obj (F i ⊗ N))) :=
    I.mapIso e₁ ≪≫ PreservesProduct.iso I (fun i => (F i ⊗ N : Rep.{0} k Γ)) ≪≫ ModuleCat.piIsoPi _
  have le : ↥(C ⊗ N : Rep.{0} k Γ).ρ.invariants ≃ₗ[k] ((i : ι) → ↥(F i ⊗ N : Rep.{0} k Γ).ρ.invariants) := e₂.toLinearEquiv
  rw [le.finrank_eq, Module.finrank_pi_fintype]

theorem injective_of_comp_eq_id {A B : Rep.{0} k Γ} (f : A ⟶ B) (g : B ⟶ A) (h : f ≫ g = 𝟙 A) : Function.Injective f.hom := by
  intro x y hxy
  have hx : (f ≫ g).hom x = x := by rw [h]; rfl
  have hy : (f ≫ g).hom y = y := by rw [h]; rfl
  change g.hom (f.hom x) = x at hx
  change g.hom (f.hom y) = y at hy
  rw [← hx, ← hy, hxy]

theorem finrank_invariants_tensor_of_iso_biprod (N A B C : Rep.{0} k Γ) (e : C ≅ A ⊞ B)
    [FiniteDimensional k A] [FiniteDimensional k B] [FiniteDimensional k N] :
    Module.finrank k (C ⊗ N : Rep.{0} k Γ).ρ.invariants =
      Module.finrank k (A ⊗ N : Rep.{0} k Γ).ρ.invariants + Module.finrank k (B ⊗ N : Rep.{0} k Γ).ρ.invariants := by
  haveI := preservesBinaryBiproducts_of_preservesBinaryProducts (Rep.invariantsFunctor k Γ)
  haveI := preservesBinaryBiproducts_of_preservesBinaryProducts (tensorRight N : Rep.{0} k Γ ⥤ Rep.{0} k Γ)
  haveI : FiniteDimensional k (A ⊗ N : Rep.{0} k Γ) := inferInstanceAs (Module.Finite k (TensorProduct k A N))
  haveI : FiniteDimensional k (B ⊗ N : Rep.{0} k Γ) := inferInstanceAs (Module.Finite k (TensorProduct k B N))
  let e₁ : C ⊗ N ≅ (A ⊗ N) ⊞ (B ⊗ N) := (tensorRight N).mapIso e ≪≫ (tensorRight N).mapBiprod A B
  let F := Rep.invariantsFunctor k Γ
  let e₂ : F.obj (C ⊗ N) ≅ ModuleCat.of k (↥(A ⊗ N : Rep.{0} k Γ).ρ.invariants × ↥(B ⊗ N : Rep.{0} k Γ).ρ.invariants) :=
    F.mapIso e₁ ≪≫ F.mapBiprod _ _ ≪≫ ModuleCat.biprodIsoProd _ _
  have le : ↥(C ⊗ N : Rep.{0} k Γ).ρ.invariants ≃ₗ[k] (↥(A ⊗ N : Rep.{0} k Γ).ρ.invariants × ↥(B ⊗ N : Rep.{0} k Γ).ρ.invariants) :=
    e₂.toLinearEquiv
  rw [le.finrank_eq, Module.finrank_prod]

theorem finiteDimensional_biprod (A B : Rep.{0} k Γ) [FiniteDimensional k A] [FiniteDimensional k B] :
    FiniteDimensional k (A ⊞ B : Rep.{0} k Γ) := by
  haveI := preservesBinaryBiproducts_of_preservesBinaryProducts (forget₂ (Rep.{0} k Γ) (ModuleCat.{0} k))
  let e : (forget₂ (Rep.{0} k Γ) (ModuleCat.{0} k)).obj (A ⊞ B) ≅ ModuleCat.of k (A × B) :=
    (forget₂ (Rep.{0} k Γ) (ModuleCat.{0} k)).mapBiprod A B ≪≫ ModuleCat.biprodIsoProd _ _
  exact Module.Finite.equiv e.toLinearEquiv.symm

end EQBXAux

theorem solution
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (K L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hK : K.IsUnramifiedOutside S) (hL : L.IsUnramifiedOutside S)
    [FiniteDimensional ℚ ↥K] [FiniteDimensional ℚ ↥L]
    (hKL : K ≤ L) [Normal ↥K ↥(levelField K L hKL)]
    (hnorm : ∀ g ∈ K.fixingSubgroup, ∀ s ∈ L.fixingSubgroup, g * s * g⁻¹ ∈ L.fixingSubgroup)
    (hcop : (L.fixingSubgroup.relIndex K.fixingSubgroup).Coprime p)
    (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p) (hζL : ζ ∈ L)
    (h4 : p = 2 → ∃ i ∈ L, i ^ 2 = -1)
    (N : Rep.{0} (ZMod p) ↥K.fixingSubgroup) [FiniteDimensional (ZMod p) N]
    (htriv : ∀ s : ↥K.fixingSubgroup, (s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ L.fixingSubgroup → N.ρ s = 1) :
    FiniteDimensional (ZMod p)
        (continuousH2Sr K.fixingSubgroup.subtype S (N.twist ((cycloChar p).comp K.fixingSubgroup.subtype))) ∧
      Module.finrank (ZMod p)
          (continuousH2Sr K.fixingSubgroup.subtype S (N.twist ((cycloChar p).comp K.fixingSubgroup.subtype))) +
        Module.finrank (ZMod p) N.ρ.invariants =
        Module.finrank (ZMod p) (sClassTorsionP K L hKL S p ⊗ N : Rep.{0} (ZMod p) ↥K.fixingSubgroup).ρ.invariants +
        ∑ q : ↥S, Module.finrank (ZMod p)
          (placesRep K L hnorm S (Sum.inr q) p ⊗ N : Rep.{0} (ZMod p) ↥K.fixingSubgroup).ρ.invariants := by
  classical

  haveI hΛ : (L.fixingSubgroup.subgroupOf K.fixingSubgroup).Normal :=
    ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      simpa using hnorm g g.2 n hn⟩
  haveI hΛf : (L.fixingSubgroup.subgroupOf K.fixingSubgroup).FiniteIndex := by
    refine ⟨fun h0 => ?_⟩
    have : L.fixingSubgroup.relIndex K.fixingSubgroup = 0 := h0
    rw [this, Nat.coprime_zero_left] at hcop
    exact (Fact.out : p.Prime).ne_one hcop

  obtain ⟨hA2, ⟨e⟩⟩ := groupCohomology.finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso S hpS K L hK hL hKL hnorm hcop ζ hζ hζL h4
  haveI := hA2

  obtain ⟨φ⟩ := groupCohomology.nonempty_continuousH2Sr_twist_linearEquiv_invariants_cyclotomicQuotientH2Rep_tensor S K L hcop N htriv
  haveI : FiniteDimensional (ZMod p) (cyclotomicQuotientH2Rep S K L p ⊗ N : Rep.{0} (ZMod p) ↥K.fixingSubgroup) :=
    inferInstanceAs (Module.Finite (ZMod p) (TensorProduct (ZMod p) (cyclotomicQuotientH2Rep S K L p) N))
  have hH : FiniteDimensional (ZMod p) (continuousH2Sr K.fixingSubgroup.subtype S (N.twist ((cycloChar p).comp K.fixingSubgroup.subtype))) :=
    LinearEquiv.finiteDimensional φ.symm
  refine ⟨hH, ?_⟩
  rw [φ.finrank_eq]

  haveI hT : FiniteDimensional (ZMod p) (Rep.trivial (ZMod p) ↥K.fixingSubgroup (ZMod p)) := inferInstanceAs (Module.Finite (ZMod p) (ZMod p))
  haveI hAB : FiniteDimensional (ZMod p) (cyclotomicQuotientH2Rep S K L p ⊞ Rep.trivial (ZMod p) ↥K.fixingSubgroup (ZMod p) : Rep.{0} (ZMod p) ↥K.fixingSubgroup) :=
    EQBXAux.finiteDimensional_biprod _ _
  haveI hCl : FiniteDimensional (ZMod p) (sClassTorsionP K L hKL S p) :=
    FiniteDimensional.of_injective (biprod.inl ≫ e.inv : sClassTorsionP K L hKL S p ⟶ _).hom.toLinearMap
      (EQBXAux.injective_of_comp_eq_id (biprod.inl ≫ e.inv) (e.hom ≫ biprod.fst) (by simp))
  haveI hPi : FiniteDimensional (ZMod p) (∏ᶜ fun q : ↥S => placesRep K L hnorm S (Sum.inr q) p : Rep.{0} (ZMod p) ↥K.fixingSubgroup) :=
    FiniteDimensional.of_injective (biprod.inr ≫ e.inv : (∏ᶜ fun q : ↥S => placesRep K L hnorm S (Sum.inr q) p) ⟶ _).hom.toLinearMap
      (EQBXAux.injective_of_comp_eq_id (biprod.inr ≫ e.inv) (e.hom ≫ biprod.snd) (by simp))
  haveI hPq : ∀ q : ↥S, FiniteDimensional (ZMod p) (placesRep K L hnorm S (Sum.inr q) p) :=
    fun q => EQBXAux.finiteDimensional_of_pi (fun q : ↥S => placesRep K L hnorm S (Sum.inr q) p) _ (Iso.refl _) q

  have h1 := EQBXAux.finrank_invariants_trivial_tensor (k := ZMod p) (Γ := ↥K.fixingSubgroup) N
  have h2 := EQBXAux.finrank_invariants_tensor_of_iso_biprod N (cyclotomicQuotientH2Rep S K L p) (Rep.trivial (ZMod p) ↥K.fixingSubgroup (ZMod p)) _ (Iso.refl _)
  have h3 := EQBXAux.finrank_invariants_tensor_of_iso_biprod N (sClassTorsionP K L hKL S p) (∏ᶜ fun q : ↥S => placesRep K L hnorm S (Sum.inr q) p) _ e
  have h4' := EQBXAux.finrank_invariants_tensor_of_iso_pi N (∏ᶜ fun q : ↥S => placesRep K L hnorm S (Sum.inr q) p)
    (fun q : ↥S => placesRep K L hnorm S (Sum.inr q) p) (Iso.refl _)
  rw [← h1, ← h2, h3, h4']

end S_groupCohomology_finiteDimensional_and_finrank_continuousH2Sr_twist_add_eq_sClassTorsionP_add_sum_placesRep
end P2MW
export P2MW.S_groupCohomology_finiteDimensional_and_finrank_continuousH2Sr_twist_add_eq_sClassTorsionP_add_sum_placesRep (solution)
