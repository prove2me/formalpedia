-- Prove2me | solution 1 for groupCohomology.exists_isPGroup_layer_inv_eq_localInv_locRes2S_div_and_sum_inv_eq_zero_of_ne_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/c2474774-ef01-5086-aeb8-7514699695da

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_GroupCohomology_LocalInvariant
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass
import Theorems.Thm_groupCohomology_continuousH2S_ofChar_cycloChar_eq_zero_of_not_mem
import Theorems.Thm_groupCohomology_exists_isGalois_isUnramifiedOutside_mem_levelCocyclesS2_continuousH2Spi_eq_of_mem
import Theorems.Thm_groupCohomology_exists_cocycles2_units_eq_pow_of_levelCocyclesS2_ofChar_cycloChar
import Theorems.Thm_NumberField_PlaceDecomp_dvd_natCard_decomp_of_pow_eq_prime
import Theorems.Thm_IsGalois_exists_intermediateField_isPGroup_and_not_dvd_finrank
import Theorems.Thm_M4aHerbrand_exists_ideleGaloisDescent_concentrated_lam_rho
import Theorems.Thm_NumberField_PlaceDecomp_exists_faithful_bridge_isBase_isLocalFundamentalClass
import Theorems.Thm_NumberField_PlaceDecomp_inv_map_lam_map_rho_res_eq_of_map_rho_res_eq_zsmul_of_forall_inv_eq
import Theorems.Thm_NumberField_PlaceDecomp_exists_int_map_res_kummer_eq_zsmul_and_localInv_locRes2S_eq
import Theorems.Thm_NumberField_PlaceDecomp_sum_sum_inv_decomp_eq_zero_of_forall_inv_eq_of_isUnramifiedOutside
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_exists_isPGroup_layer_inv_eq_localInv_locRes2S_div_and_sum_inv_eq_zero_of_ne_two
p2m_attr_erase "instance" "AlgebraicClosure.Rat.isGalois IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap"
p2m_attr_erase "instance" "M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion NumberField.AdelicHaar.locallyCompactSpace_adeleRing NumberField.AdelicHaar.finite_residueField_adicCompletionIntegers NumberField.AdelicHaar.locallyCompactSpace_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_finiteAdeleRing NumberField.AdelicHaar.compactSpace_adicCompletionIntegers NumberField.AdelicHaar.t2Space_finiteAdeleRing NumberField.AdelicHaar.t2Space_matrix_adeleRing NumberField.AdelicHaar.t2Space_adeleRing NumberField.AdelicHaar.fact_isOpen_adicCompletionIntegers NumberField.AdelicHaar.t2Space_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_matrix_adeleRing NumberField.AdelicHaar.t2Space_infiniteAdeleRing NumberField.AdelicHaar.properSpace_adicCompletion M4aHerbrand.Bridge.instT2SpaceAdeleRing ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal groupCohomology.Kummer.instMulDistribMulActionRootsOfUnity LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite Deep.NTSupply.instNormalRayClassSubgroup instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal"
p2m_attr_erase "simp" "SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq"
p2m_attr_erase "simp" "M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq M4aHerbrand.Bridge.finiteConorm_apply M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe"
p2m_attr_erase "simp" "Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply IsLocalRing.principalUnits_zero groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk groupCohomology.Kummer.coe_kummerCocycleRoots groupCohomology.Kummer.mem_powerSubgroup_iff groupCohomology.Kummer.val_smul_units groupCohomology.Kummer.kummerHom_apply groupCohomology.Kummer.coe_smul_rootsOfUnity GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply"
p2m_attr_erase "simp" "NumberField.SUnits.coe_unitOfValuedEqOne NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl NumberField.SUnits.val_zsmul NumberField.SUnits.val_add LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
open CategoryTheory Module groupCohomology ExtCitation NumberField IsDedekindDomain M4aHerbrand
open scoped NumberField.PlaceDecomp

section Assembly
set_option synthInstance.maxHeartbeats 1600000
open CategoryTheory Module groupCohomology ExtCitation NumberField IsDedekindDomain M4aHerbrand
open scoped NumberField.PlaceDecomp

private theorem finite_setOf_natCast_mem (E : Type) [Field E] [NumberField E] (q : ℕ) [Fact q.Prime] :
    {v : HeightOneSpectrum (𝓞 E) | (q : 𝓞 E) ∈ v.asIdeal}.Finite := by
  have hq0 : (Ideal.span {(q : 𝓞 E)} : Ideal (𝓞 E)) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out : q.Prime).ne_zero
  refine (Ideal.finite_factors hq0).subset fun v hv => ?_
  simp only [Set.mem_setOf_eq] at hv ⊢
  exact (Ideal.dvd_iff_le).2 ((Ideal.span_singleton_le_iff_mem _).2 hv)

private theorem natPrime_eq_of_mem_of_mem (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))
    (q q' : ℕ) [hq : Fact q.Prime] [hq' : Fact q'.Prime] (h : (q : 𝓞 K) ∈ w.asIdeal) (h' : (q' : 𝓞 K) ∈ w.asIdeal) : q' = q := by
  by_contra hne
  have hcop : Nat.Coprime q' q := (Nat.coprime_primes hq'.out hq.out).2 hne
  have h1 : (1 : 𝓞 K) ∈ w.asIdeal := by
    obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hcop
    have e1 : ((a : ℤ) : 𝓞 K) * (q' : 𝓞 K) + ((b : ℤ) : 𝓞 K) * (q : 𝓞 K) = 1 := by exact_mod_cast congrArg (fun z : ℤ => (z : 𝓞 K)) hab
    rw [← e1]
    exact w.asIdeal.add_mem (w.asIdeal.mul_mem_left _ h') (w.asIdeal.mul_mem_left _ h)
  exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)

set_option maxHeartbeats 12800000 in
theorem solution
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hp2 : p ≠ 2)
    (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p)
    (c : continuousH2S S (ofChar (k := ZMod p) (cycloChar p)))
    (hc : locRes₂S S (ofChar (k := ZMod p) (cycloChar p)) (extArithLoc S (Sum.inl ())) c = 0) :
    ∃ (E F : Type) (_ : Field E) (_ : NumberField E) (_ : Field F) (_ : NumberField F) (_ : Algebra E F)
      (_ : IsGalois E F) (_ : ¬ p ∣ Module.finrank ℚ E)
    (_ : IsPGroup p (F ≃ₐ[E] F))
    (D : IdeleGaloisDescent (𝓞 F) E F)
    (_ : MulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))
    (_ : ∀ (g : F ≃ₐ[E] F) (c : IdeleClassGroup (𝓞 F) F), g • c = D.classAct g c)
    (ι : ∀ w : HeightOneSpectrum (𝓞 F), (w.adicCompletion F)ˣ →* (AdeleRing (𝓞 F) F)ˣ)
    (_ : ∀ (w : HeightOneSpectrum (𝓞 F)) (x : (w.adicCompletion F)ˣ),
      finPart w (ι w x) = x ∧ (∀ w' : HeightOneSpectrum (𝓞 F), w' ≠ w → finPart w' (ι w x) = 1) ∧ infPart (ι w x) = 1)
    (lam : ∀ w : HeightOneSpectrum (𝓞 F),
      Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ ⟶
        Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype
          (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)))
    (_ : ∀ (w : HeightOneSpectrum (𝓞 F)) (x : (w.adicCompletion F)ˣ),
      (lam w).hom (Additive.ofMul x) = Additive.ofMul (QuotientGroup.mk (ι w x) : IdeleClassGroup (𝓞 F) F))
    (x : groupCohomology.H2 (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) Fˣ))
    (ρ : ∀ w : HeightOneSpectrum (𝓞 F),
      Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) Fˣ) ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)
    (_ : ∀ (w : HeightOneSpectrum (𝓞 F)) (u : Fˣ),
      (ρ w).hom (Additive.ofMul u) =
        Additive.ofMul (Units.map (algebraMap F (w.adicCompletion F)).toMonoidHom u))
    (V : ↥S → Finset (HeightOneSpectrum (𝓞 E)))
    (_ : ∀ (q : ↥S) (v : HeightOneSpectrum (𝓞 E)), v ∈ V q ↔ (((q : Nat.Primes) : ℕ) : 𝓞 E) ∈ v.asIdeal),
    ∀
    (invG : ↥(groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) 2) →+
      AddCircle (1 : ℚ))
    (inv : ∀ H : Subgroup (F ≃ₐ[E] F),
      ↥(groupCohomology (Rep.res H.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))) 2) →+
        AddCircle (1 : ℚ))

    (_ : Function.Injective invG)
    (_ : ∀ H : Subgroup (F ≃ₐ[E] F), Function.Injective (inv H))
    (_ : ∀ t : AddCircle (1 : ℚ), t ∈ invG.range ↔ Nat.card (F ≃ₐ[E] F) • t = 0)
    (_ : ∀ (H : Subgroup (F ≃ₐ[E] F)) (t : AddCircle (1 : ℚ)), t ∈ (inv H).range ↔ Nat.card ↥H • t = 0)

    (_ : ∀ (H : Subgroup (F ≃ₐ[E] F))
      (x : ↥(groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) 2)),
      inv H ((groupCohomology.map H.subtype
        (𝟙 (Rep.res H.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)))) 2).hom x) =
          H.index • invG x)

    (_ : ∀ (w : HeightOneSpectrum (𝓞 F))
        (q : ℕ) [Fact q.Prime] (L' : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L']
        [MulSemiringAction (↥(NumberField.PlaceDecomp.decomp E F w)) L']
        [MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (↥L')ˣ]
        (Φ : w.adicCompletion F ≃+* L')
        (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w)) (x : ℚ_[q]),
          g • algebraMap ℚ_[q] L' x = algebraMap ℚ_[q] L' x)
        (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w)) (v : (↥L')ˣ), ((g • v : (↥L')ˣ) : L') = g • (v : L'))
        (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w)) (x : w.adicCompletion F), Φ (g • x) = g • Φ x)
        (K₀ : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K₀]
        (_ : ExtCitation.LocalLevel.IsBase q L' (↥(NumberField.PlaceDecomp.decomp E F w)) K₀)
        (θ : Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (↥L')ˣ ⟶
          Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)
        (_ : ∀ v : (↥L')ˣ,
          ((Additive.toMul (θ.hom (Additive.ofMul v)) : (w.adicCompletion F)ˣ) : w.adicCompletion F) = Φ.symm (v : L'))
        (u' : groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (↥L')ˣ))
        (_ : ExtCitation.LocalLevel.IsLocalFundamentalClass q L' (↥(NumberField.PlaceDecomp.decomp E F w)) K₀ u'),
        inv (NumberField.PlaceDecomp.decomp E F w)
            ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F w)) (lam w) 2).hom
              ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F w)) θ 2).hom u')) =
          (((1 : ℚ) / (Nat.card ↥(NumberField.PlaceDecomp.decomp E F w) : ℚ) : ℚ) : AddCircle (1 : ℚ)))

    (_ : ∀ x : ↥(groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) 2),
        invG x = inv ⊤ ((groupCohomology.map (⊤ : Subgroup (F ≃ₐ[E] F)).subtype
          (𝟙 (Rep.res (⊤ : Subgroup (F ≃ₐ[E] F)).subtype
            (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)))) 2).hom x)),

      (∀ (w : HeightOneSpectrum (𝓞 F)) (q : ↥S), (((q : Nat.Primes) : ℕ) : 𝓞 F) ∈ w.asIdeal →
          inv (NumberField.PlaceDecomp.decomp E F w)
            ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F w)) (lam w) 2).hom
              ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F w)) (ρ w) 2).hom
                ((groupCohomology.map (NumberField.PlaceDecomp.decomp E F w).subtype
                  (𝟙 (Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype
                    (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) Fˣ))) 2).hom x))) =
          ((((Ideal.ramificationIdx' (Ideal.span {(((q : Nat.Primes) : ℕ) : ℤ)})
                (Ideal.comap (algebraMap (𝓞 E) (𝓞 F)) w.asIdeal) *
              Ideal.inertiaDeg' (Ideal.span {(((q : Nat.Primes) : ℕ) : ℤ)})
                (Ideal.comap (algebraMap (𝓞 E) (𝓞 F)) w.asIdeal) *
              ZMod.val
                (haveI : Fact (((q : Nat.Primes) : ℕ)).Prime := ⟨(q : Nat.Primes).prop⟩
                localInv p ζ (q : Nat.Primes)
                (locRes₂S S (ofChar (k := ZMod p) (cycloChar p)) (extArithLoc S (Sum.inr q)) c))
              : ℕ) : ℚ) / (p : ℚ) : ℚ) : AddCircle (1 : ℚ))) ∧

      (∀ w : ↥S → HeightOneSpectrum (𝓞 E) → HeightOneSpectrum (𝓞 F),
        (∀ (q : ↥S) (v : HeightOneSpectrum (𝓞 E)), v ∈ V q →
          Ideal.comap (algebraMap (𝓞 E) (𝓞 F)) (w q v).asIdeal = v.asIdeal) →
        ∑ q : ↥S, ∑ v ∈ V q,
          inv (NumberField.PlaceDecomp.decomp E F (w q v))
            ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F (w q v))) (lam (w q v)) 2).hom
              ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F (w q v))) (ρ (w q v)) 2).hom
                ((groupCohomology.map (NumberField.PlaceDecomp.decomp E F (w q v)).subtype
                  (𝟙 (Rep.res (NumberField.PlaceDecomp.decomp E F (w q v)).subtype
                    (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) Fˣ))) 2).hom x))) = 0) := by
  classical

  have mkV : ∀ (E : Type) [Field E] [NumberField E], ∃ V : ↥S → Finset (HeightOneSpectrum (𝓞 E)),
      ∀ (q : ↥S) (v : HeightOneSpectrum (𝓞 E)), v ∈ V q ↔ (((q : Nat.Primes) : ℕ) : 𝓞 E) ∈ v.asIdeal := by
    intro E _ _
    refine ⟨fun q => (haveI : Fact (((q : Nat.Primes) : ℕ)).Prime := ⟨(q : Nat.Primes).prop⟩; finite_setOf_natCast_mem E ((q : Nat.Primes) : ℕ)).toFinset, fun q v => ?_⟩
    exact Set.Finite.mem_toFinset _
  by_cases hpS : pPrime p ∈ S
  ·
    obtain ⟨F₀, hfd, hgal, hF₀, hζF₀, hroots, f, hf, hfc, hconst⟩ :=
      groupCohomology.exists_isGalois_isUnramifiedOutside_mem_levelCocyclesS2_continuousH2Spi_eq_of_mem S hpS ζ hζ c
    haveI := hfd
    haveI := hgal
    haveI : NumberField ↥F₀ := NumberField.mk
    obtain ⟨E₀, hPG, hpE⟩ := IsGalois.exists_intermediateField_isPGroup_and_not_dvd_finrank ℚ ↥F₀ p
    haveI : NumberField ↥E₀ := NumberField.mk
    obtain ⟨D, instAct, hact, ι, hι, lam, hlam, ρ, hρ⟩ :=
      M4aHerbrand.exists_ideleGaloisDescent_concentrated_lam_rho ↥E₀ ↥F₀
    obtain ⟨V, hV⟩ := mkV ↥E₀
    letI := instAct

    obtain ⟨-, -, -, -, -, -, -, ρℚ, hρℚ⟩ := M4aHerbrand.exists_ideleGaloisDescent_concentrated_lam_rho ℚ ↥F₀

    let e : ↥F₀ →ₐ[ℚ] AlgebraicClosure ℚ := F₀.val
    have hζ0 : (⟨ζ, hζF₀⟩ : ↥F₀) ≠ 0 := fun h =>
      hζ.ne_zero (Fact.out : p.Prime).ne_zero (congrArg Subtype.val h)
    let ζF : (↥F₀)ˣ := Units.mk0 ⟨ζ, hζF₀⟩ hζ0
    have hζF : e (ζF : ↥F₀) = ζ := rfl
    have hconst' : ∀ g g' s s' : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
        (∀ y : ↥F₀, s (e y) = e y) → (∀ y : ↥F₀, s' (e y) = e y) → f (g * s, g' * s') = f (g, g') :=
      fun g g' s s' hs hs' => hconst g g' s s'
        ((IntermediateField.mem_fixingSubgroup_iff _ _).2 fun y hy => hs ⟨y, hy⟩)
        ((IntermediateField.mem_fixingSubgroup_iff _ _).2 fun y hy => hs' ⟨y, hy⟩)
    obtain ⟨b, hb, hbc⟩ :=
      groupCohomology.exists_cocycles2_units_eq_pow_of_levelCocyclesS2_ofChar_cycloChar S ζ hζ f hf ↥F₀ e ζF hζF hconst'
    let xℚ : groupCohomology.H2 (Rep.ofMulDistribMulAction (↥F₀ ≃ₐ[ℚ] ↥F₀) (↥F₀)ˣ) :=
      (H2π (Rep.ofMulDistribMulAction (↥F₀ ≃ₐ[ℚ] ↥F₀) (↥F₀)ˣ)).hom ⟨b, hbc⟩
    let r : (↥F₀ ≃ₐ[↥E₀] ↥F₀) →* (↥F₀ ≃ₐ[ℚ] ↥F₀) :=
      { toFun := fun g => g.restrictScalars ℚ
        map_one' := AlgEquiv.ext fun _ => rfl
        map_mul' := fun _ _ => AlgEquiv.ext fun _ => rfl }
    have hr : ∀ (g : ↥F₀ ≃ₐ[↥E₀] ↥F₀) (y : ↥F₀), r g y = g y := fun _ _ => rfl
    let φ : Rep.res r (Rep.ofMulDistribMulAction (↥F₀ ≃ₐ[ℚ] ↥F₀) (↥F₀)ˣ) ⟶ Rep.ofMulDistribMulAction (↥F₀ ≃ₐ[↥E₀] ↥F₀) (↥F₀)ˣ :=
      Rep.ofHom ⟨LinearMap.id, fun g => LinearMap.ext fun u => rfl⟩
    have hφ : ∀ u : (↥F₀)ˣ, φ.hom (Additive.ofMul u) = Additive.ofMul u := fun _ => rfl
    let x : groupCohomology.H2 (Rep.ofMulDistribMulAction (↥F₀ ≃ₐ[↥E₀] ↥F₀) (↥F₀)ˣ) := (groupCohomology.map r φ 2).hom xℚ
    refine ⟨↥E₀, ↥F₀, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, hpE, hPG,
      D, instAct, hact, ι, hι, lam, hlam, x, ρ, hρ, V, hV, ?_⟩
    intro invG inv hinjG hinj hrangeG hrange hres hloc htop

    have ha : ∀ (w : HeightOneSpectrum (𝓞 ↥F₀)) (q : ↥S), (((q : Nat.Primes) : ℕ) : 𝓞 ↥F₀) ∈ w.asIdeal →
        inv (NumberField.PlaceDecomp.decomp ↥E₀ ↥F₀ w)
          ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp ↥E₀ ↥F₀ w)) (lam w) 2).hom
            ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp ↥E₀ ↥F₀ w)) (ρ w) 2).hom
              ((groupCohomology.map (NumberField.PlaceDecomp.decomp ↥E₀ ↥F₀ w).subtype
                (𝟙 (Rep.res (NumberField.PlaceDecomp.decomp ↥E₀ ↥F₀ w).subtype
                  (Rep.ofMulDistribMulAction (↥F₀ ≃ₐ[↥E₀] ↥F₀) (↥F₀)ˣ))) 2).hom x))) =
        ((((Ideal.ramificationIdx' (Ideal.span {(((q : Nat.Primes) : ℕ) : ℤ)})
              (Ideal.comap (algebraMap (𝓞 ↥E₀) (𝓞 ↥F₀)) w.asIdeal) *
            Ideal.inertiaDeg' (Ideal.span {(((q : Nat.Primes) : ℕ) : ℤ)})
              (Ideal.comap (algebraMap (𝓞 ↥E₀) (𝓞 ↥F₀)) w.asIdeal) *
            ZMod.val
                (haveI : Fact (((q : Nat.Primes) : ℕ)).Prime := ⟨(q : Nat.Primes).prop⟩
                localInv p ζ (q : Nat.Primes)
                (locRes₂S S (ofChar (k := ZMod p) (cycloChar p)) (extArithLoc S (Sum.inr q)) c)) : ℕ) : ℚ) / (p : ℚ) : ℚ) : AddCircle (1 : ℚ)) := by
      intro w q hwq
      haveI : Fact (((q : Nat.Primes) : ℕ)).Prime := ⟨(q : Nat.Primes).prop⟩
      obtain ⟨q', instq', hw', L', instfd, instMSA, instF, instMDA, Φ', hΦ1, hΦ2, hΦ3, K₀, instK₀, hK₀, θ', hθ', u', hu'⟩ :=
        NumberField.PlaceDecomp.exists_faithful_bridge_isBase_isLocalFundamentalClass ℚ ↥F₀ w
      haveI := instq'
      have hqq : q' = ((q : Nat.Primes) : ℕ) := natPrime_eq_of_mem_of_mem ↥F₀ w _ _ hwq hw'
      subst hqq
      letI := instfd; letI := instMSA; letI := instF; letI := instMDA; letI := instK₀

      obtain ⟨rt, hrtF, hrt⟩ := hroots q
      have hrt' : ((⟨rt, hrtF⟩ : ↥F₀) : ↥F₀) ^ p = (((q : Nat.Primes) : ℕ) : ↥F₀) := Subtype.ext (by
        rw [SubmonoidClass.coe_pow]; exact hrt)
      have hpD : p ∣ Nat.card ↥(NumberField.PlaceDecomp.decomp ℚ ↥F₀ w) :=
        NumberField.PlaceDecomp.dvd_natCard_decomp_of_pow_eq_prime ↥F₀ p ((q : Nat.Primes) : ℕ) _ hrt' w hwq

      obtain ⟨m, hm, hlocm⟩ :=
        NumberField.PlaceDecomp.exists_int_map_res_kummer_eq_zsmul_and_localInv_locRes2S_eq S q ζ hζ c f hf hfc
          F₀ ζF rfl hconst b (fun g h ĝ ĥ hg hh => hb g h ĝ ĥ hg hh) hbc w hwq hpD (ρℚ w) (hρℚ w)
          L' Φ' hΦ1 hΦ2 hΦ3 K₀ hK₀ θ' hθ' u' hu'
      have key := NumberField.PlaceDecomp.inv_map_lam_map_rho_res_eq_of_map_rho_res_eq_zsmul_of_forall_inv_eq
        ↥E₀ ↥F₀ r hr p w ((q : Nat.Primes) : ℕ) hwq hpD xℚ φ hφ x rfl (ρℚ w) (hρℚ w) (ρ w) (hρ w)
        L' Φ' hΦ1 hΦ2 hΦ3 K₀ hK₀ θ' hθ' u' hu' m hm (lam w) inv (hloc w ((q : Nat.Primes) : ℕ))
      rw [key, hlocm]
    refine ⟨ha, ?_⟩

    have hζp : ζF ^ p = 1 := by
      apply Units.ext
      apply Subtype.ext
      show ((((ζF ^ p : (↥F₀)ˣ) : ↥F₀)) : AlgebraicClosure ℚ) = (((1 : (↥F₀)ˣ) : ↥F₀) : AlgebraicClosure ℚ)
      rw [Units.val_pow_eq_pow_val, Units.val_one]
      push_cast
      exact hζ.pow_eq_one
    exact NumberField.PlaceDecomp.sum_sum_inv_decomp_eq_zero_of_forall_inv_eq_of_isUnramifiedOutside S hp2 F₀ hF₀ E₀ hPG
      D instAct hact ι hι lam hlam ρ hρ V hV f ζF hζp b (fun g h ĝ ĥ hg hh => hb g h ĝ ĥ hg hh) hbc r hr φ hφ x rfl
      invG inv hinjG hinj hrangeG hrange hres hloc htop
      (fun q => ZMod.val
                (haveI : Fact (((q : Nat.Primes) : ℕ)).Prime := ⟨(q : Nat.Primes).prop⟩
                localInv p ζ (q : Nat.Primes)
                (locRes₂S S (ofChar (k := ZMod p) (cycloChar p)) (extArithLoc S (Sum.inr q)) c))) ha

  ·
    have hc0 : c = 0 := groupCohomology.continuousH2S_ofChar_cycloChar_eq_zero_of_not_mem S hp2 hpS c
    subst hc0
    obtain ⟨D, instAct, hact, ι, hι, lam, hlam, ρ, hρ⟩ :=
      M4aHerbrand.exists_ideleGaloisDescent_concentrated_lam_rho ℚ ℚ
    obtain ⟨V, hV⟩ := mkV ℚ
    letI := instAct
    have htriv : IsPGroup p (ℚ ≃ₐ[ℚ] ℚ) := IsPGroup.of_card (n := 0) (by
      rw [pow_zero, Nat.card_eq_fintype_card, Fintype.card_eq_one_iff]; exact ⟨1, fun g => Subsingleton.elim _ _⟩)
    have hdeg : ¬ p ∣ Module.finrank ℚ ℚ := by
      rw [Module.finrank_self]; exact (Fact.out : p.Prime).one_lt.ne' ∘ Nat.eq_one_of_dvd_one
    refine ⟨ℚ, ℚ, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, hdeg, htriv,
      D, instAct, hact, ι, hι, lam, hlam, 0, ρ, hρ, V, hV, ?_⟩
    intro invG inv hinjG hinj hrangeG hrange hres hloc htop
    refine ⟨?_, ?_⟩
    · intro w q hwq
      haveI : Fact (((q : Nat.Primes) : ℕ)).Prime := ⟨(q : Nat.Primes).prop⟩
      have h0 : localInv p ζ (q : Nat.Primes)
          (locRes₂S S (ofChar (k := ZMod p) (cycloChar p)) (extArithLoc S (Sum.inr q)) 0) = 0 := by
        rw [LinearMap.map_zero]
        exact LinearMap.map_zero _
      simp only [map_zero] at h0 ⊢
      rw [h0, ZMod.val_zero, mul_zero, Nat.cast_zero, zero_div, AddCircle.coe_zero]
    · intro wsel hwsel
      simp only [map_zero, Finset.sum_const_zero]
end Assembly

end S_groupCohomology_exists_isPGroup_layer_inv_eq_localInv_locRes2S_div_and_sum_inv_eq_zero_of_ne_two
end P2MW
export P2MW.S_groupCohomology_exists_isPGroup_layer_inv_eq_localInv_locRes2S_div_and_sum_inv_eq_zero_of_ne_two (solution)
