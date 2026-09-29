-- Prove2me | solution 1 for groupCohomology.sum_localInv_locRes2S_eq_zero_of_ne_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/89fdec81-ff76-53d2-bbf7-23c76080e6de

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_GroupCohomology_LocalInvariant
import Theorems.Thm_M4aHerbrand_exists_invariant_groupCohomology_ideleClassGroup_of_isPGroup_of_ne_two
import Theorems.Thm_groupCohomology_exists_isPGroup_layer_inv_eq_localInv_locRes2S_div_and_sum_inv_eq_zero_of_ne_two
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_sum_localInv_locRes2S_eq_zero_of_ne_two
p2m_attr_erase "instance" "FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing"
p2m_attr_erase "instance" "M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion NumberField.AdelicHaar.locallyCompactSpace_adeleRing NumberField.AdelicHaar.finite_residueField_adicCompletionIntegers NumberField.AdelicHaar.locallyCompactSpace_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_finiteAdeleRing NumberField.AdelicHaar.compactSpace_adicCompletionIntegers NumberField.AdelicHaar.t2Space_finiteAdeleRing NumberField.AdelicHaar.t2Space_matrix_adeleRing NumberField.AdelicHaar.t2Space_adeleRing NumberField.AdelicHaar.fact_isOpen_adicCompletionIntegers NumberField.AdelicHaar.t2Space_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_matrix_adeleRing NumberField.AdelicHaar.t2Space_infiniteAdeleRing NumberField.AdelicHaar.properSpace_adicCompletion M4aHerbrand.Bridge.instT2SpaceAdeleRing LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite Deep.NTSupply.instNormalRayClassSubgroup instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal AlgebraicClosure.Rat.isGalois groupCohomology.Kummer.instMulDistribMulActionRootsOfUnity"
p2m_attr_erase "simp" "GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl NumberField.SUnits.val_zsmul NumberField.SUnits.val_add M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq M4aHerbrand.Bridge.finiteConorm_apply SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul"
p2m_attr_erase "simp" "SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply"
p2m_attr_erase "simp" "IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq IsLocalRing.principalUnits_zero Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk"
p2m_attr_erase "simp" "LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec groupCohomology.Kummer.coe_kummerCocycleRoots groupCohomology.Kummer.mem_powerSubgroup_iff groupCohomology.Kummer.val_smul_units groupCohomology.Kummer.kummerHom_apply groupCohomology.Kummer.coe_smul_rootsOfUnity"

set_option autoImplicit false
open CategoryTheory Module groupCohomology ExtCitation

section BodyUnits

open IsDedekindDomain NumberField Finset

namespace BrSumUnits

section placesAboveRationalPrime

variable {K : Type*} [Field K]

private theorem span_natCast_isMaximal (q : ℕ) [hq : Fact q.Prime] : (Ideal.span {(q : ℤ)}).IsMaximal :=
  PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hq.out).irreducible

private theorem span_natCast_ne_bot (q : ℕ) [hq : Fact q.Prime] : (Ideal.span {(q : ℤ)} : Ideal ℤ) ≠ ⊥ := by
  rw [Ne, Ideal.span_singleton_eq_bot]
  exact_mod_cast hq.out.ne_zero

private theorem mem_primesOver_span_iff (q : ℕ) [hq : Fact q.Prime] (P : Ideal (𝓞 K)) :
    P ∈ (Ideal.span {(q : ℤ)}).primesOver (𝓞 K) ↔ P.IsPrime ∧ ((q : ℕ) : 𝓞 K) ∈ P := by
  simp only [Ideal.primesOver, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hP, hover⟩
    refine ⟨hP, ?_⟩
    have hmem : (q : ℤ) ∈ Ideal.under ℤ P := hover.over ▸ Ideal.mem_span_singleton_self _
    simpa using hmem
  · rintro ⟨hP, hqP⟩
    refine ⟨hP, ⟨?_⟩⟩
    have hle : Ideal.span {(q : ℤ)} ≤ Ideal.under ℤ P := by
      rw [Ideal.span_singleton_le_iff_mem]
      simpa using hqP
    exact (span_natCast_isMaximal q).eq_of_le (Ideal.comap_ne_top _ hP.ne_top) hle

private theorem ne_bot_of_natCast_mem [NumberField K] (q : ℕ) [hq : Fact q.Prime] {P : Ideal (𝓞 K)}
    (h : ((q : ℕ) : 𝓞 K) ∈ P) :
    P ≠ ⊥ := by
  rintro rfl
  exact (Nat.cast_ne_zero.mpr hq.out.ne_zero) ((Ideal.mem_bot).mp h)

private theorem sum_ramificationIdx_mul_inertiaDeg_eq_finrank [NumberField K] (q : ℕ) [hq : Fact q.Prime]
    (T : Finset (HeightOneSpectrum (𝓞 K))) (hT : ∀ v, v ∈ T ↔ ((q : ℕ) : 𝓞 K) ∈ v.asIdeal) :
    ∑ v ∈ T, Ideal.ramificationIdx' (Ideal.span {(q : ℤ)}) v.asIdeal *
        Ideal.inertiaDeg' (Ideal.span {(q : ℤ)}) v.asIdeal = Module.finrank ℚ K := by
  haveI := span_natCast_isMaximal q
  rw [← Ideal.sum_ramification_inertia (𝓞 K) ℚ K (span_natCast_ne_bot q)]
  have himg : T.image HeightOneSpectrum.asIdeal =
      IsDedekindDomain.primesOverFinset (Ideal.span {(q : ℤ)}) (𝓞 K) := by
    ext P
    rw [IsDedekindDomain.mem_primesOverFinset_iff (span_natCast_ne_bot q), Finset.mem_image]
    rw [mem_primesOver_span_iff]
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨v.isPrime, (hT v).mp hv⟩
    · rintro ⟨hprime, hq_mem⟩
      exact ⟨⟨P, hprime, ne_bot_of_natCast_mem q hq_mem⟩, (hT _).mpr hq_mem, rfl⟩
  rw [← himg, Finset.sum_image (fun v _ w _ h => HeightOneSpectrum.ext h)]

end placesAboveRationalPrime

section circleArithmetic

variable {p : ℕ} [hp : Fact p.Prime]

private noncomputable def valDiv (c : ZMod p) : AddCircle (1 : ℚ) := (((c.val : ℚ) / p : ℚ) : AddCircle (1 : ℚ))

private theorem valDiv_add (a b : ZMod p) : valDiv (a + b) = valDiv a + valDiv b := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  unfold valDiv
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  rw [← AddCircle.coe_add, ← sub_eq_zero, ← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff, ZMod.val_add]
  obtain ⟨d, hd⟩ : ∃ d : ℕ, (a.val + b.val) % p + p * d = a.val + b.val := ⟨_, Nat.mod_add_div _ _⟩
  refine ⟨-(d : ℤ), ?_⟩
  have hq : (((a.val + b.val) % p : ℕ) : ℚ) + (p : ℚ) * (d : ℚ) = (a.val : ℚ) + (b.val : ℚ) := by
    exact_mod_cast hd
  rw [zsmul_eq_mul, mul_one, Int.cast_neg, Int.cast_natCast]
  field_simp
  linear_combination -hq

private noncomputable def valDivHom : ZMod p →+ AddCircle (1 : ℚ) where
  toFun := valDiv
  map_zero' := by simp [valDiv]
  map_add' := valDiv_add

private theorem valDivHom_apply (c : ZMod p) : valDivHom c = (((c.val : ℚ) / p : ℚ) : AddCircle (1 : ℚ)) := rfl

private theorem sum_sum_natCast_mul_val_div_eq {ι : Type*} [Fintype ι] {κ : Type*} (V : ι → Finset κ)
    (ef : ι → κ → ℕ) (a : ι → ZMod p) (n : ℕ) (hV : ∀ s, ∑ v ∈ V s, ef s v = n) :
    ∑ s, ∑ v ∈ V s, ((((ef s v * (a s).val : ℕ) : ℚ) / p : ℚ) : AddCircle (1 : ℚ)) =
      ((((n * (∑ s, a s).val : ℕ) : ℚ) / p : ℚ) : AddCircle (1 : ℚ)) := by
  have hsmul : ∀ (m : ℕ) (c : ZMod p),
      ((((m * c.val : ℕ) : ℚ) / p : ℚ) : AddCircle (1 : ℚ)) = valDivHom (m • c) := by
    intro m c
    induction m with
    | zero => simp [valDivHom_apply]
    | succ m ih =>
      rw [add_smul, one_smul, map_add, ← ih, valDivHom_apply, ← AddCircle.coe_add]
      congr 1
      push_cast
      ring
  simp_rw [hsmul]
  have hinner : ∀ s, ∑ v ∈ V s, valDivHom (ef s v • a s) = valDivHom (n • a s) := fun s => by
    rw [← map_sum, ← Finset.sum_smul, hV s]
  simp_rw [hinner]
  rw [← map_sum, Finset.smul_sum]

private theorem eq_zero_of_natCast_mul_val_div_eq_zero (n : ℕ) (hn : ¬ p ∣ n) (b : ZMod p)
    (h : ((((n * b.val : ℕ) : ℚ) / p : ℚ) : AddCircle (1 : ℚ)) = 0) : b = 0 := by
  rw [AddCircle.coe_eq_zero_iff] at h
  obtain ⟨k, hk⟩ := h
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hk' : ((n * b.val : ℕ) : ℤ) = k * p := by
    have h1 : (k : ℚ) = ((n * b.val : ℕ) : ℚ) / p := by simpa using hk
    have h2 : ((n * b.val : ℕ) : ℚ) = k * p := by rw [h1]; field_simp
    exact_mod_cast h2
  have hdvd : p ∣ n * b.val := by
    have : (p : ℤ) ∣ ((n * b.val : ℕ) : ℤ) := ⟨k, by rw [hk', mul_comm]⟩
    exact_mod_cast this
  rcases (Nat.Prime.dvd_mul hp.out).mp hdvd with hpn | hpb
  · exact absurd hpn hn
  · exact (ZMod.val_eq_zero b).mp (Nat.eq_zero_of_dvd_of_lt hpb (ZMod.val_lt b))

end circleArithmetic

section conclusion

variable {p : ℕ} [hp : Fact p.Prime]

private theorem exists_heightOneSpectrum_comap_eq {E F : Type*} [Field E] [NumberField E] [Field F]
    [NumberField F] [Algebra E F] (v : HeightOneSpectrum (𝓞 E)) :
    ∃ w : HeightOneSpectrum (𝓞 F), Ideal.comap (algebraMap (𝓞 E) (𝓞 F)) w.asIdeal = v.asIdeal := by
  haveI := v.isPrime
  obtain ⟨Q, hQ, hQv⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := 𝓞 F) v.asIdeal
    (by rw [RingOfIntegers.ker_algebraMap_eq_bot E F]; exact bot_le)
  refine ⟨⟨Q, hQ, ?_⟩, hQv⟩
  rintro rfl
  exact v.ne_bot (by rw [← hQv, Ideal.comap_bot_of_injective _ ((RingHom.injective_iff_ker_eq_bot _).mpr
    (RingOfIntegers.ker_algebraMap_eq_bot E F))])

private theorem natCast_mem_of_comap_eq {E F : Type*} [Field E] [Field F] [Algebra E F] (n : ℕ)
    {v : HeightOneSpectrum (𝓞 E)} {w : HeightOneSpectrum (𝓞 F)}
    (hw : Ideal.comap (algebraMap (𝓞 E) (𝓞 F)) w.asIdeal = v.asIdeal) (hv : (n : 𝓞 E) ∈ v.asIdeal) :
    (n : 𝓞 F) ∈ w.asIdeal := by
  rw [← hw, Ideal.mem_comap, map_natCast] at hv
  exact hv

private theorem sum_eq_zero_of_sum_sum_eq_zero {E : Type*} [Field E] [NumberField E] (S : Finset Nat.Primes)
    (V : ↥S → Finset (HeightOneSpectrum (𝓞 E)))
    (hV : ∀ (q : ↥S) (v : HeightOneSpectrum (𝓞 E)), v ∈ V q ↔ (((q : Nat.Primes) : ℕ) : 𝓞 E) ∈ v.asIdeal)
    (hpE : ¬ p ∣ Module.finrank ℚ E) (a : ↥S → ZMod p)
    (t : ↥S → HeightOneSpectrum (𝓞 E) → AddCircle (1 : ℚ))
    (ht : ∀ (q : ↥S), ∀ v ∈ V q, t q v =
      ((((Ideal.ramificationIdx' (Ideal.span {(((q : Nat.Primes) : ℕ) : ℤ)}) v.asIdeal *
            Ideal.inertiaDeg' (Ideal.span {(((q : Nat.Primes) : ℕ) : ℤ)}) v.asIdeal * ZMod.val (a q) : ℕ) : ℚ) /
          (p : ℚ) : ℚ) : AddCircle (1 : ℚ)))
    (hsum : ∑ q : ↥S, ∑ v ∈ V q, t q v = 0) :
    ∑ q : ↥S, a q = 0 := by
  have hU1 : ∀ q : ↥S, ∑ v ∈ V q,
      Ideal.ramificationIdx' (Ideal.span {(((q : Nat.Primes) : ℕ) : ℤ)}) v.asIdeal *
        Ideal.inertiaDeg' (Ideal.span {(((q : Nat.Primes) : ℕ) : ℤ)}) v.asIdeal = Module.finrank ℚ E := by
    intro q
    haveI : Fact (((q : Nat.Primes) : ℕ)).Prime := ⟨(q : Nat.Primes).prop⟩
    exact sum_ramificationIdx_mul_inertiaDeg_eq_finrank _ (V q) (hV q)
  rw [Finset.sum_congr rfl (fun q _ => Finset.sum_congr rfl (fun v hv => ht q v hv)),
    sum_sum_natCast_mul_val_div_eq V
      (fun q v => Ideal.ramificationIdx' (Ideal.span {(((q : Nat.Primes) : ℕ) : ℤ)}) v.asIdeal *
        Ideal.inertiaDeg' (Ideal.span {(((q : Nat.Primes) : ℕ) : ℤ)}) v.asIdeal) a _ hU1] at hsum
  exact eq_zero_of_natCast_mul_val_div_eq_zero _ hpE _ hsum

end conclusion

end BrSumUnits

end BodyUnits

theorem solution
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hp2 : p ≠ 2)
    (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p)
    (c : continuousH2S S (ofChar (k := ZMod p) (cycloChar p)))
    (hc : locRes₂S S (ofChar (k := ZMod p) (cycloChar p)) (extArithLoc S (Sum.inl ())) c = 0) :
    ∑ q : ↥S,
      (haveI : Fact (((q : Nat.Primes) : ℕ)).Prime := ⟨(q : Nat.Primes).prop⟩
      localInv p ζ (q : Nat.Primes)
        (locRes₂S S (ofChar (k := ZMod p) (cycloChar p)) (extArithLoc S (Sum.inr q)) c)) = 0 := by
  obtain ⟨E, F, instFE, instNE, instFF, instNF, instAlg, instGal, hpE, hG, D, instAct, hact, ι, hι, lam, hlam, x, ρ,
      hρ, V, hV, hpkg⟩ :=
    groupCohomology.exists_isPGroup_layer_inv_eq_localInv_locRes2S_div_and_sum_inv_eq_zero_of_ne_two S hp2 ζ hζ c hc
  obtain ⟨invG, inv, hinjG, hinj, hrangeG, hrange, hres, hloc, htop⟩ :=
    M4aHerbrand.exists_invariant_groupCohomology_ideleClassGroup_of_isPGroup_of_ne_two E F p hp2 hG D hact ι hι lam hlam
  obtain ⟨ha, hb⟩ := hpkg invG inv hinjG hinj hrangeG hrange hres hloc htop
  choose w hw using fun (_ : ↥S) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)) =>
    BrSumUnits.exists_heightOneSpectrum_comap_eq (F := F) v
  have hsum := hb w fun q v _ => hw q v
  refine BrSumUnits.sum_eq_zero_of_sum_sum_eq_zero S V hV hpE _ _ ?_ hsum
  intro q v hv
  have h := ha (w q v) q (BrSumUnits.natCast_mem_of_comap_eq _ (hw q v) ((hV q v).1 hv))
  rw [hw q v] at h
  exact h

end S_groupCohomology_sum_localInv_locRes2S_eq_zero_of_ne_two
end P2MW
export P2MW.S_groupCohomology_sum_localInv_locRes2S_eq_zero_of_ne_two (solution)
