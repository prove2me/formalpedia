-- Prove2me | solution 1 for groupCohomology.continuousH2Sr_galoisSUnitsRep_eq_zero_of_forall_res_extArithIndex_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/188fa31d-ce75-5da4-a20f-d525f04c69a0

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Definitions.Def_GroupCohomology_ContinuousH2Map
import Definitions.Def_GroupCohomology_LevelSubgroup
import Definitions.Def_GroupCohomology_GaloisSUnits
import Definitions.Def_NumberField_SUnitsMax
import Theorems.Thm_groupCohomology_eq_zero_of_forall_continuousH2Map_primeLocal_eq_zero_pPrimary_continuousH2Sr_sUnitsMax
import Theorems.Thm_groupCohomology_bijective_continuousH2SrMap_sUnitsMaxRep_galoisSUnitsRep
import Theorems.Thm_groupCohomology_mem_levelCoboundaries2_sUnitsMaxRep_of_zsmul_mem_of_val_mem
import Theorems.Thm_IntermediateField_IsUnramifiedOutside_sup_adjoin_simple_of_pow_mem
import Theorems.Thm_groupCohomology_continuousH2Sr_galoisSUnitsRep_eq_zero_of_res_adjoin_sqrt_neg_one_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_continuousH2Sr_galoisSUnitsRep_eq_zero_of_forall_res_extArithIndex_eq_zero
p2m_attr_erase "instance" "AlgebraicClosure.Rat.isGalois IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap"
p2m_attr_erase "instance" "M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion NumberField.AdelicHaar.locallyCompactSpace_adeleRing NumberField.AdelicHaar.finite_residueField_adicCompletionIntegers NumberField.AdelicHaar.locallyCompactSpace_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_finiteAdeleRing NumberField.AdelicHaar.compactSpace_adicCompletionIntegers NumberField.AdelicHaar.t2Space_finiteAdeleRing NumberField.AdelicHaar.t2Space_matrix_adeleRing NumberField.AdelicHaar.t2Space_adeleRing NumberField.AdelicHaar.fact_isOpen_adicCompletionIntegers NumberField.AdelicHaar.t2Space_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_matrix_adeleRing NumberField.AdelicHaar.t2Space_infiniteAdeleRing NumberField.AdelicHaar.properSpace_adicCompletion M4aHerbrand.Bridge.instT2SpaceAdeleRing M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite Deep.NTSupply.instNormalRayClassSubgroup instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar"
p2m_attr_erase "instance" "ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal"
p2m_attr_erase "simp" "NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq groupCohomology.continuousH2Inflation_H2π groupCohomology.levelInflate₂_apply groupCohomology.coe_levelInflateCocycles₂ groupCohomology.levelInflate₁_apply SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply"
p2m_attr_erase "simp" "IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq M4aHerbrand.Bridge.finiteConorm_apply M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul"
p2m_attr_erase "simp" "RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk"
p2m_attr_erase "simp" "M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk M4aHerbrand.IdeleGaloisDescent.classAct_mk Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent IsLocalRing.principalUnits_zero ExtCitation.LocalLevel.coe_smul_OO WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open CategoryTheory groupCohomology ValuationSubring NumberField.LevelArith ExtCitation

noncomputable section

local instance isAlgebraicQbar_hp : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
local instance isAlgClosureQbar_hp : IsAlgClosure ℚ (AlgebraicClosure ℚ) := ⟨inferInstance, inferInstance⟩
local instance normalQbar_hp : Normal ℚ (AlgebraicClosure ℚ) := IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)
local instance isGaloisQbar_hp : IsGalois ℚ (AlgebraicClosure ℚ) := IsAlgClosure.isGalois ℚ (AlgebraicClosure ℚ)

namespace P2MHasseP

local notation "ℚb" => (AlgebraicClosure ℚ)
local notation "Γ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

section Coeff

variable (S : Finset Nat.Primes)

lemma not_liesOverPrime_of_liesOverPrime (A : ValuationSubring ℚb) {q q' : ℕ} (hq : q.Prime) (hq' : q'.Prime) (hne : q ≠ q')
    (h : A.LiesOverPrime q) : ¬ A.LiesOverPrime q' := by
  intro h'
  rw [LiesOverPrime, ValuationSubring.mem_nonunits_iff] at h h'
  have hcop : Nat.Coprime q q' := (Nat.coprime_primes hq hq').2 hne
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hcop
  have hint : ∀ z : ℤ, A.valuation (z : ℚb) ≤ 1 := fun z => (A.valuation_le_one_iff _).2 (by simp)
  have h1 : A.valuation ((a : ℚb) * q + (b : ℚb) * q') < 1 := by
    refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ ?_)
    · rw [Valuation.map_mul]; exact mul_lt_one_of_nonneg_of_lt_one_right (hint a) zero_le' h
    · rw [Valuation.map_mul]; exact mul_lt_one_of_nonneg_of_lt_one_right (hint b) zero_le' h'
  have h2 : ((a : ℚb) * q + (b : ℚb) * q') = 1 := by exact_mod_cast hab
  rw [h2, Valuation.map_one] at h1
  exact lt_irrefl _ h1

lemma valuation_ratCast_eq_one (A : ValuationSubring ℚb) (hA : ∀ q : ℕ, q.Prime → ¬ A.LiesOverPrime q) (r : ℚ) (hr : r ≠ 0) :
    A.valuation (r : ℚb) = 1 := by
  have hnat : ∀ n : ℕ, n ≠ 0 → A.valuation (n : ℚb) = 1 := by
    intro n
    induction n using Nat.recOnMul with
    | zero => intro h; exact absurd rfl h
    | one => intro; simp
    | prime q hq =>
      intro
      have h := hA q hq
      rw [LiesOverPrime, ValuationSubring.mem_nonunits_iff, not_lt] at h
      exact le_antisymm ((A.valuation_le_one_iff _).2 (by simp)) h
    | mul a b ha hb =>
      intro hab
      rw [Nat.cast_mul, Valuation.map_mul, ha (left_ne_zero_of_mul hab), hb (right_ne_zero_of_mul hab), one_mul]
  have hint : ∀ z : ℤ, z ≠ 0 → A.valuation (z : ℚb) = 1 := by
    intro z hz
    have := hnat z.natAbs (Int.natAbs_ne_zero.2 hz)
    rcases Int.natAbs_eq z with h | h
    · rw [h, Int.cast_natCast]; rw [h, Int.natAbs_natCast] at this; exact this
    · rw [h, Int.cast_neg, Valuation.map_neg, Int.cast_natCast]
      rw [h, Int.natAbs_neg, Int.natAbs_natCast] at this; exact this
  have e : (r : ℚb) = (r.num : ℚb) / (r.den : ℚb) := by
    rw [← Rat.cast_intCast, ← Rat.cast_natCast, ← Rat.cast_div, Rat.num_div_den]
  rw [e, map_div₀, hint _ (Rat.num_ne_zero.2 hr), hnat _ r.den_nz, div_one]

lemma valuation_le_one_of_forall_not_liesOverPrime (A : ValuationSubring ℚb) (hA : ∀ q : ℕ, q.Prime → ¬ A.LiesOverPrime q)
    (y : ℚb) : A.valuation y ≤ 1 := by
  by_contra hy
  rw [not_le] at hy
  obtain ⟨f, hf0, hfy⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) y)

  obtain ⟨n, hn⟩ : ∃ n, f.natDegree = n := ⟨_, rfl⟩
  have hlead : f.coeff n ≠ 0 := by rw [← hn]; exact Polynomial.leadingCoeff_ne_zero.2 hf0
  have hval_coeff : ∀ i, f.coeff i ≠ 0 → A.valuation (algebraMap ℚ ℚb (f.coeff i)) = 1 := fun i hi =>
    valuation_ratCast_eq_one A hA _ hi
  have hsum : Polynomial.aeval y f = ∑ i ∈ Finset.range (n + 1), algebraMap ℚ ℚb (f.coeff i) * y ^ i := by
    rw [Polynomial.aeval_eq_sum_range, hn]
    simp only [Algebra.smul_def]
  have hlt : ∀ i ∈ Finset.range n, A.valuation (algebraMap ℚ ℚb (f.coeff i) * y ^ i) < A.valuation y ^ n := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [Valuation.map_mul, Valuation.map_pow]
    by_cases hc : f.coeff i = 0
    · rw [hc, map_zero, Valuation.map_zero, zero_mul]; exact pow_pos (lt_trans zero_lt_one hy) _
    · rw [hval_coeff i hc, one_mul]; exact pow_lt_pow_right₀ hy hi
  have htop : A.valuation (algebraMap ℚ ℚb (f.coeff n) * y ^ n) = A.valuation y ^ n := by
    rw [Valuation.map_mul, Valuation.map_pow, hval_coeff n hlead, one_mul]
  have hne : A.valuation (∑ i ∈ Finset.range n, algebraMap ℚ ℚb (f.coeff i) * y ^ i) < A.valuation y ^ n := by
    refine Valuation.map_sum_lt _ (pow_ne_zero _ (ne_of_gt (lt_trans zero_lt_one hy))) hlt
  have : A.valuation (Polynomial.aeval y f) = A.valuation y ^ n := by
    rw [hsum, Finset.sum_range_succ, Valuation.map_add_eq_of_lt_right, htop]
    rwa [htop]
  rw [hfy, Valuation.map_zero] at this
  exact absurd this.symm (pow_ne_zero _ (ne_of_gt (lt_trans zero_lt_one hy)))

lemma mem_galoisSUnits_of_mem_sUnitsMax {x : ℚbˣ} (hx : x ∈ sUnitsMax S) : x ∈ galoisSUnits S := by
  intro A hA
  by_cases hex : ∃ q : ℕ, q.Prime ∧ A.LiesOverPrime q
  · obtain ⟨q, hq, hAq⟩ := hex
    have hqS : (⟨q, hq⟩ : Nat.Primes) ∉ S := fun h => hA _ h hAq
    exact hx.2 ⟨q, hq⟩ hqS A hAq
  · push Not at hex
    exact ⟨(A.valuation_le_one_iff _).1 (valuation_le_one_of_forall_not_liesOverPrime A hex _),
      (A.valuation_le_one_iff _).1 (valuation_le_one_of_forall_not_liesOverPrime A hex _)⟩

variable (F : IntermediateField ℚ ℚb)

set_option hygiene false in
local notation "U" => IntermediateField.fixingSubgroup F

abbrev SUn : Rep ℤ ↥U := Rep.res (U).subtype (galoisSUnitsRep S)

abbrev ES : Rep ℤ ↥U := sUnitsMaxRep S F

def φE : ES S F →ₗ[ℤ] SUn S F where
  toFun x := Additive.ofMul ⟨sUnitsMaxRep.val S F x, mem_galoisSUnits_of_mem_sUnitsMax S (sUnitsMaxStable_le S F x.2)⟩
  map_add' x y := rfl
  map_smul' c x := by
    apply Additive.toMul.injective
    apply Subtype.ext
    simp only [toMul_ofMul, RingHom.id_apply]
    rfl

lemma φE_val (x : ES S F) : ((Additive.toMul (φE S F x) : ↥(galoisSUnits S)) : ℚbˣ) = sUnitsMaxRep.val S F x := rfl

lemma φE_ρ (g : ↥U) (a : ES S F) : φE S F ((ES S F).ρ g a) = (SUn S F).ρ g (φE S F a) := rfl

lemma galoisSUnitsToUnits_φE (x : ES S F) : galoisSUnitsToUnits S (φE S F x) = (x.1 : Additive ℚbˣ) := rfl

abbrev Φ : continuousH2Sr (U).subtype S (ES S F) →ₗ[ℤ] continuousH2Sr (U).subtype S (SUn S F) :=
  continuousH2SrMap (rH := (U).subtype) (rG := (U).subtype) (A := ES S F) (B := SUn S F)
    (MonoidHom.id ↥U) (fun _ => rfl) S (φE S F) (φE_ρ S F)

lemma Φ_bijective (hF : F.IsUnramifiedOutside S) : Function.Bijective (Φ S F) :=
  groupCohomology.bijective_continuousH2SrMap_sUnitsMaxRep_galoisSUnitsRep S F hF (φE S F) (φE_val S F) (φE_ρ S F)

end Coeff

section Cochains

lemma conj_cocycle_identity {k G : Type} [CommRing k] [Group G] {M : Rep k G} (A : G × G → M) (hA : A ∈ cocycles₂ M)
    (s a b : G) :
    M.ρ s (A (s⁻¹ * a * s, s⁻¹ * b * s)) - A (a, b) =
      M.ρ a (A (s, s⁻¹ * b * s) - A (b, s)) - (A (s, s⁻¹ * (a * b) * s) - A (a * b, s)) + (A (s, s⁻¹ * a * s) - A (a, s)) := by
  rw [mem_cocycles₂_iff] at hA
  have h1 := hA a b s
  have h2 := hA a s (s⁻¹ * b * s)
  have h3 := hA s (s⁻¹ * a * s) (s⁻¹ * b * s)
  have e2 : s * (s⁻¹ * b * s) = b * s := by group
  have e3 : s * (s⁻¹ * a * s) = a * s := by group
  have e3' : s⁻¹ * a * s * (s⁻¹ * b * s) = s⁻¹ * (a * b) * s := by group
  rw [e2] at h2
  rw [e3, e3'] at h3
  have f3 : M.ρ s (A (s⁻¹ * a * s, s⁻¹ * b * s)) = A (a * s, s⁻¹ * b * s) + A (s, s⁻¹ * a * s) - A (s, s⁻¹ * (a * b) * s) := by
    rw [eq_sub_iff_add_eq]; exact h3.symm
  have f2 : A (a * s, s⁻¹ * b * s) = M.ρ a (A (s, s⁻¹ * b * s)) + A (a, b * s) - A (a, s) := by
    rw [eq_sub_iff_add_eq]; exact h2
  have f1 : A (a, b * s) = A (a * b, s) + A (a, b) - M.ρ a (A (b, s)) := by
    rw [eq_sub_iff_add_eq, add_comm (A (a, b * s))]; exact h1.symm
  rw [f3, f2, f1, map_sub]
  abel

abbrev Un (D : Subgroup Γ) : Rep ℤ ↥D := Rep.res D.subtype (Rep.ofAlgebraAutOnUnits ℚ ℚb)

def actΓ (g : Γ) : Additive ℚbˣ →+ Additive ℚbˣ := (MulDistribMulAction.toMonoidHom ℚbˣ g).toAdditive

lemma actΓ_apply (g : Γ) (x : Additive ℚbˣ) : actΓ g x = Additive.ofMul (g • Additive.toMul x) := rfl

lemma actΓ_mul (g h : Γ) (x : Additive ℚbˣ) : actΓ (g * h) x = actΓ g (actΓ h x) := by
  simp only [actΓ_apply, toMul_ofMul, mul_smul]

lemma Un_ρ (D : Subgroup Γ) (g : ↥D) (x : Additive ℚbˣ) : (Un D).ρ g x = actΓ (g : Γ) x := rfl

lemma exists_normal_level (F' : IntermediateField ℚ ℚb) [FiniteDimensional ℚ F'] :
    ∃ F'' : IntermediateField ℚ ℚb, FiniteDimensional ℚ F'' ∧ F''.fixingSubgroup.Normal ∧
      F''.fixingSubgroup ≤ F'.fixingSubgroup := by
  haveI : Normal ℚ (IntermediateField.normalClosure ℚ F' ℚb) := by
    have := normalClosure.normal ℚ (↥F') ℚb; convert this <;> first | rfl | exact Subsingleton.elim _ _
  refine ⟨IntermediateField.normalClosure ℚ F' ℚb, inferInstance, ?_,
    IntermediateField.fixingSubgroup_antitone (IntermediateField.le_normalClosure F')⟩
  have := groupCohomology.normal_comap_fixingSubgroup (MonoidHom.id Γ) (IntermediateField.normalClosure ℚ F' ℚb)
  rwa [Subgroup.comap_id] at this

lemma finiteDimensional_sup' {E E' : IntermediateField ℚ ℚb} (h : FiniteDimensional ℚ E) (h' : FiniteDimensional ℚ E') :
    FiniteDimensional ℚ (↥(E ⊔ E')) := by
  have := @IntermediateField.finiteDimensional_sup ℚ ℚb _ _ _ E E' (by convert h) (by convert h')
  convert this

variable (F : IntermediateField ℚ ℚb)

set_option hygiene false in
local notation "U" => IntermediateField.fixingSubgroup F

structure IsGood (V : ↥U × ↥U → Additive ℚbˣ) : Prop where
  cocycle : V ∈ cocycles₂ (Un (U))
  level : IsLevelConstant₂ (U).subtype V

def HasLocalCob (V : ↥U × ↥U → Additive ℚbˣ) (D : Subgroup Γ) (hD : D ≤ U) : Prop :=
  ∃ ψ : ↥D → Additive ℚbˣ, IsLevelConstant₁ D.subtype ψ ∧
    (d₁₂ (Un D)).hom ψ = fun g => V (Subgroup.inclusion hD g.1, Subgroup.inclusion hD g.2)

variable {F}

lemma HasLocalCob.mono {V : ↥U × ↥U → Additive ℚbˣ} {D D' : Subgroup Γ} {hD : D ≤ U} (h : HasLocalCob F V D hD)
    (hle : D' ≤ D) : HasLocalCob F V D' (hle.trans hD) := by
  obtain ⟨ψ, hψl, hψd⟩ := h
  refine ⟨ψ ∘ Subgroup.inclusion hle, IsLevelConstant₁.precomp (rH := D.subtype) (rG := D'.subtype)
    (Subgroup.inclusion hle) (fun _ => rfl) hψl, ?_⟩
  funext g
  have := congrFun hψd (Subgroup.inclusion hle g.1, Subgroup.inclusion hle g.2)
  rw [d₁₂_hom_apply] at this ⊢
  exact this

lemma HasLocalCob.transport {V : ↥U × ↥U → Additive ℚbˣ} (hV : IsGood F V) {D₁ D₂ : Subgroup Γ} {h₁ : D₁ ≤ U} (h₂ : D₂ ≤ U)
    (f : ↥U) (hf : ∀ d ∈ D₂, ((f : Γ)⁻¹ * d * f) ∈ D₁) (h : HasLocalCob F V D₁ h₁) : HasLocalCob F V D₂ h₂ := by
  obtain ⟨ψ₁, ⟨F₁, hF₁, hc₁⟩, hψ₁d⟩ := h
  haveI := hF₁

  let u : ↥D₂ → ↥U := fun d => Subgroup.inclusion h₂ d
  let c : ↥D₂ →* ↥D₁ :=
    { toFun := fun d => ⟨(f : Γ)⁻¹ * d * f, hf d d.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun d d' => Subtype.ext (by
        simp only [Subgroup.coe_mul]
        group) }
  have hcu : ∀ d : ↥D₂, Subgroup.inclusion h₁ (c d) = f⁻¹ * u d * f := fun d => rfl

  let Hh : ↥U → Additive ℚbˣ := fun g => V (f, f⁻¹ * g * f) - V (g, f)
  let ψ₂ : ↥D₂ → Additive ℚbˣ := fun d => actΓ (f : Γ) (ψ₁ (c d)) - Hh (u d)
  refine ⟨ψ₂, ?_, ?_⟩
  ·
    obtain ⟨F₂, hF₂, hc₂⟩ := hV.level
    haveI := hF₂
    obtain ⟨F₃, hF₃, hN, hle⟩ := exists_normal_level (F₁ ⊔ F₂)
    have h31 : F₃.fixingSubgroup ≤ F₁.fixingSubgroup := hle.trans (IntermediateField.fixingSubgroup_antitone le_sup_left)
    have h32 : F₃.fixingSubgroup ≤ F₂.fixingSubgroup := hle.trans (IntermediateField.fixingSubgroup_antitone le_sup_right)
    refine ⟨F₃, hF₃, fun d s hs => ?_⟩
    have hs' : ((f : Γ)⁻¹ * (s : Γ) * f) ∈ F₃.fixingSubgroup := hN.conj_mem' _ hs _
    have e1 : ψ₁ (c (d * s)) = ψ₁ (c d) := by
      rw [map_mul]; exact hc₁ _ _ (h31 hs')
    have e2 : Hh (u (d * s)) = Hh (u d) := by
      simp only [Hh, u]
      have eu : Subgroup.inclusion h₂ (d * s) = Subgroup.inclusion h₂ d * Subgroup.inclusion h₂ s := map_mul _ _ _
      rw [eu]
      have ea : f⁻¹ * (Subgroup.inclusion h₂ d * Subgroup.inclusion h₂ s) * f =
          f⁻¹ * Subgroup.inclusion h₂ d * f * (f⁻¹ * Subgroup.inclusion h₂ s * f) := by group
      rw [ea]
      have t1 := hc₂ f (f⁻¹ * Subgroup.inclusion h₂ d * f) 1 (f⁻¹ * Subgroup.inclusion h₂ s * f) (Subgroup.one_mem _) (h32 hs')
      rw [mul_one] at t1
      have t2 := hc₂ (Subgroup.inclusion h₂ d) f (Subgroup.inclusion h₂ s) 1 (h32 hs) (Subgroup.one_mem _)
      rw [mul_one] at t2
      rw [t1, t2]
    simp only [ψ₂]
    rw [e1, e2]
  ·
    funext g
    obtain ⟨d₁, d₂⟩ := g
    rw [d₁₂_hom_apply, Un_ρ]
    have hψ := congrFun hψ₁d (c d₁, c d₂)
    rw [d₁₂_hom_apply, Un_ρ] at hψ
    dsimp only at hψ
    rw [hcu, hcu] at hψ
    replace hψ : (actΓ ((c d₁ : ↥D₁) : Γ)) (ψ₁ (c d₂)) - ψ₁ (c d₁ * c d₂) + ψ₁ (c d₁) =
        V (f⁻¹ * u d₁ * f, f⁻¹ * u d₂ * f) := hψ
    have key := conj_cocycle_identity (M := Un (U)) V hV.cocycle f (u d₁) (u d₂)
    rw [Un_ρ, Un_ρ] at key
    replace key : (actΓ (f : Γ)) (V (f⁻¹ * u d₁ * f, f⁻¹ * u d₂ * f)) - V (u d₁, u d₂) =
        (actΓ ((u d₁ : ↥U) : Γ)) (V (f, f⁻¹ * u d₂ * f) - V (u d₂, f)) - (V (f, f⁻¹ * (u d₁ * u d₂) * f) - V (u d₁ * u d₂, f))
          + (V (f, f⁻¹ * u d₁ * f) - V (u d₁, f)) := key

    have eu : u (d₁ * d₂) = u d₁ * u d₂ := map_mul (Subgroup.inclusion h₂) d₁ d₂
    have lhs : actΓ ((d₁ : Γ)) (ψ₂ d₂) - ψ₂ (d₁ * d₂) + ψ₂ d₁ =
        actΓ (f : Γ) (actΓ ((c d₁ : ↥D₁) : Γ) (ψ₁ (c d₂)) - ψ₁ (c d₁ * c d₂) + ψ₁ (c d₁))
          - (actΓ ((u d₁ : ↥U) : Γ) (Hh (u d₂)) - Hh (u d₁ * u d₂) + Hh (u d₁)) := by
      simp only [ψ₂, map_sub, map_add, ← actΓ_mul, map_mul, eu]
      have ec : (f : Γ) * (((c d₁ : ↥D₁)) : Γ) = ((d₁ : Γ)) * (f : Γ) := by
        change (f : Γ) * ((f : Γ)⁻¹ * d₁ * f) = _; group
      rw [ec]
      change _ = _ - (actΓ (d₁ : Γ) (Hh (u d₂)) - _ + _)
      abel
    change actΓ ((d₁ : Γ)) (ψ₂ d₂) - ψ₂ (d₁ * d₂) + ψ₂ d₁ = V (u d₁, u d₂)
    rw [lhs, hψ]
    simp only [Hh]
    rw [← key]
    abel

section PiForms

variable {k : Type} [CommRing k] {G H I : Type} [Group G] [Group H] [Group I]
variable {rI : I →* Γ} {rH : H →* Γ} {rG : G →* Γ}

lemma map_srTo_π_eq_zero_iff (S : Finset Nat.Primes) {A : Rep k H} {B : Rep k G} (f : G →* H) (hf : ∀ g, rH (f g) = rG g)
    (φ : A →ₗ[k] B) (hφ : ∀ (g : G) (a : A), φ (A.ρ (f g) a) = B.ρ g (φ a)) (α : ↥(levelCocyclesSr₂ rH S A)) :
    continuousH2Map f hf φ hφ (continuousH2SrToContinuousH2 rH S A (continuousH2Srπ rH S A α)) = 0 ↔
      cochainsPullPush₂ f φ (α : H × H → A) ∈ levelCoboundaries₂ rG B :=
  continuousH2π_eq_zero_iff _ _ _

lemma map_srTo_srMap_π_eq_zero_iff (S : Finset Nat.Primes) {A : Rep k I} {A' : Rep k H} {B : Rep k G}
    (f' : H →* I) (hf' : ∀ h, rI (f' h) = rH h) (φ' : A →ₗ[k] A') (hφ' : ∀ (h : H) (a : A), φ' (A.ρ (f' h) a) = A'.ρ h (φ' a))
    (f : G →* H) (hf : ∀ g, rH (f g) = rG g)
    (φ : A' →ₗ[k] B) (hφ : ∀ (g : G) (a : A'), φ (A'.ρ (f g) a) = B.ρ g (φ a)) (α : ↥(levelCocyclesSr₂ rI S A)) :
    continuousH2Map f hf φ hφ (continuousH2SrToContinuousH2 rH S A'
        (continuousH2SrMap f' hf' S φ' hφ' (continuousH2Srπ rI S A α))) = 0 ↔
      cochainsPullPush₂ f φ (cochainsPullPush₂ f' φ' (α : I × I → A)) ∈ levelCoboundaries₂ rG B :=
  continuousH2π_eq_zero_iff _ _ _

lemma srMap_π_eq_zero_iff (S : Finset Nat.Primes) {A : Rep k I} {A' : Rep k H}
    (f' : H →* I) (hf' : ∀ h, rI (f' h) = rH h) (φ' : A →ₗ[k] A') (hφ' : ∀ (h : H) (a : A), φ' (A.ρ (f' h) a) = A'.ρ h (φ' a))
    (α : ↥(levelCocyclesSr₂ rI S A)) :
    continuousH2SrMap f' hf' S φ' hφ' (continuousH2Srπ rI S A α) = 0 ↔
      cochainsPullPush₂ f' φ' (α : I × I → A) ∈ levelCoboundariesSr₂ rH S A' :=
  continuousH2Srπ_eq_zero_iff _ _ _ _

lemma zsmul_π_eq_zero_iff (S : Finset Nat.Primes) {A : Rep k H} (n : ℤ) (α : ↥(levelCocyclesSr₂ rH S A)) :
    n • continuousH2Srπ rH S A α = 0 ↔ n • (α : H × H → A) ∈ levelCoboundariesSr₂ rH S A := by
  rw [← map_zsmul, continuousH2Srπ_eq_zero_iff, Submodule.coe_smul_of_tower]

end PiForms

end Cochains

section AllSigma

variable (F : IntermediateField ℚ ℚb) [IsGalois ℚ F]

set_option hygiene false in
local notation "U" => IntermediateField.fixingSubgroup F

scoped instance normal_U : Subgroup.Normal U := by
  have := groupCohomology.normal_comap_fixingSubgroup (MonoidHom.id Γ) F
  rwa [Subgroup.comap_id] at this

lemma hasLocalCob_all {V : ↥U × ↥U → Additive ℚbˣ} (hV : IsGood F V) (K : Subgroup Γ)
    (γ : Γ ⧸ ((U) ⊔ K) → Γ) (hγ : ∀ t, (γ t : Γ ⧸ ((U) ⊔ K)) = t)
    (h : ∀ t, HasLocalCob F V ((U) ⊓ K.map (MulAut.conj (γ t)).toMonoidHom) inf_le_left) (σ : Γ) :
    HasLocalCob F V ((U) ⊓ K.map (MulAut.conj σ).toMonoidHom) inf_le_left := by
  set γ₀ : Γ := γ (σ : Γ ⧸ ((U) ⊔ K)) with hγ₀
  have hmem : γ₀⁻¹ * σ ∈ (U) ⊔ K := by rw [← QuotientGroup.eq, hγ]
  have hmem' : γ₀⁻¹ * σ ∈ (((U) ⊔ K : Subgroup Γ) : Set Γ) := hmem
  rw [Subgroup.normal_mul] at hmem'
  obtain ⟨u, hu, k, hk, huk⟩ := Set.mem_mul.1 hmem'

  have hfU : γ₀ * u * γ₀⁻¹ ∈ U := (normal_U F).conj_mem _ hu _
  have hσ : σ = γ₀ * u * γ₀⁻¹ * γ₀ * k := by
    have : σ = γ₀ * (γ₀⁻¹ * σ) := by group
    rw [this, ← huk]; group
  let f : ↥U := ⟨γ₀ * u * γ₀⁻¹, hfU⟩
  refine HasLocalCob.transport hV inf_le_left f (fun d hd => ?_) (h (σ : Γ ⧸ ((U) ⊔ K)))
  refine ⟨(normal_U F).conj_mem' _ hd.1 f, ?_⟩
  obtain ⟨k₀, hk₀, hd₂⟩ := Subgroup.mem_map.1 hd.2
  refine Subgroup.mem_map.2 ⟨k * k₀ * k⁻¹, K.mul_mem (K.mul_mem hk hk₀) (K.inv_mem hk), ?_⟩
  rw [← hd₂]
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, f]
  rw [← hγ₀, hσ]
  group

end AllSigma

section H4

variable {p : ℕ} [hp : Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
variable (F : IntermediateField ℚ ℚb)

set_option hygiene false in
local notation "U" => IntermediateField.fixingSubgroup F

abbrev Dq (q : ↥S) (σ : Γ) : Subgroup Γ := (U) ⊓ ((extArithLoc S (Sum.inr q)).range.map (MulAut.conj σ).toMonoidHom)

def vα (α : ↥U × ↥U → ES S F) : ↥U × ↥U → Additive ℚbˣ := fun g => ((α g : ES S F).1 : Additive ℚbˣ)

lemma isGood_vα (α : ↥(levelCocyclesSr₂ (U).subtype S (ES S F))) : IsGood F (vα S F α) := by
  obtain ⟨hc, hl⟩ := (mem_levelCocyclesSr₂_iff _ _ _ _).1 α.2
  refine ⟨(mem_cocycles₂_iff (A := Un (U)) _).2 fun g h j => ?_, hl.isLevelConstant₂.comp _⟩
  rw [mem_cocycles₂_iff] at hc
  have := congrArg (fun e : ES S F => (e.1 : Additive ℚbˣ)) (hc g h j)
  first | simpa using this | (have h_1 := this; simp at h_1; exact h_1) | (have h_1 := this; simp at h_1 ⊢; exact h_1) | exact (this)

include hpS in

theorem A_h4 (hF : F.IsUnramifiedOutside S) (h4 : p = 2 → ∃ i ∈ F, i ^ 2 = -1)
    (x : continuousH2Sr (U).subtype S (SUn S F)) (hx : (p : ℤ) • x = 0)
    (hall : ∀ (q : ↥S) (σ : Γ),
      continuousH2Map (rH := (U).subtype) (rG := (Dq S F q σ).subtype) (A := SUn S F) (B := Un (Dq S F q σ))
        (Subgroup.inclusion inf_le_left) (fun _ => rfl) (galoisSUnitsToUnits S) (fun _ _ => rfl)
        (continuousH2SrToContinuousH2 (U).subtype S (SUn S F) x) = 0) :
    x = 0 := by
  haveI : FiniteDimensional ℚ F := hF.1
  obtain ⟨a, rfl⟩ := (Φ_bijective S F hF).2 x
  have hpa : (p : ℤ) • a = 0 := (Φ_bijective S F hF).1 (by rw [map_smul, map_zero]; exact hx)
  suffices ha0 : a = 0 by rw [ha0, map_zero]
  have hat : a ∈ Submodule.torsion' ℤ (continuousH2Sr (U).subtype S (ES S F)) (Submonoid.powers (p : ℤ)) :=
    (Submodule.mem_torsion'_iff _ _).2 ⟨⟨(p : ℤ), Submonoid.mem_powers _⟩, hpa⟩
  refine groupCohomology.eq_zero_of_forall_continuousH2Map_primeLocal_eq_zero_pPrimary_continuousH2Sr_sUnitsMax
    S hpS F hF h4 a hat fun q σ => ?_
  obtain ⟨α, rfl⟩ := continuousH2Srπ_surjective _ _ _ a
  refine (map_srTo_π_eq_zero_iff S _ _ _ _ α).2 ?_

  let ℓ : primeLocalGaloisGroup (q : Nat.Primes) →* Γ := (MulAut.conj σ).toMonoidHom.comp (primeLocalToGlobal (q : Nat.Primes))
  have hDle : Dq S F q σ ≤ U := inf_le_left
  let X : ↥(Dq S F q σ) × ↥(Dq S F q σ) → ES S F :=
    cochainsPullPush₂ (A := ES S F) (B := Rep.res (Subgroup.inclusion hDle) (ES S F)) (Subgroup.inclusion hDle) LinearMap.id α
  have hX : X ∈ levelCocycles₂ (Dq S F q σ).subtype (Rep.res (Subgroup.inclusion hDle) (ES S F)) :=
    cochainsPullPush₂_mem_levelCocycles₂ (rH := (U).subtype) (rG := (Dq S F q σ).subtype) (A := ES S F)
      (B := Rep.res (Subgroup.inclusion hDle) (ES S F)) (Subgroup.inclusion hDle) (fun _ => rfl) LinearMap.id
      (fun _ _ => rfl) (levelCocyclesSr₂_le_levelCocycles₂ _ _ _ α.2)
  have hpX : (p : ℤ) • X ∈ levelCoboundaries₂ (Dq S F q σ).subtype (Rep.res (Subgroup.inclusion hDle) (ES S F)) := by
    have h1 : (p : ℤ) • (α : ↥U × ↥U → ES S F) ∈ levelCoboundariesSr₂ (U).subtype S (ES S F) :=
      (zsmul_π_eq_zero_iff S (p : ℤ) α).1 hpa
    have h2 := cochainsPullPush₂_mem_levelCoboundaries₂ (rH := (U).subtype) (rG := (Dq S F q σ).subtype) (A := ES S F)
      (B := Rep.res (Subgroup.inclusion hDle) (ES S F)) (Subgroup.inclusion hDle) (fun _ => rfl) LinearMap.id
      (fun _ _ => rfl) (levelCoboundariesSr₂_le_levelCoboundaries₂ _ _ _ h1)
    rw [map_zsmul] at h2
    exact h2
  have hval : (fun g => Additive.ofMul (sUnitsMaxRep.val S F (X g)) : ↥(Dq S F q σ) × ↥(Dq S F q σ) → Additive ℚbˣ) ∈
      levelCoboundaries₂ (Dq S F q σ).subtype (Un (Dq S F q σ)) :=
    (map_srTo_srMap_π_eq_zero_iff S _ _ _ _ _ _ _ _ α).1 (hall q σ)
  have hXcob := groupCohomology.mem_levelCoboundaries2_sUnitsMaxRep_of_zsmul_mem_of_val_mem S hpS F (Dq S F q σ) hDle X hX hpX hval
  obtain ⟨ψD, hψDl, hψDd⟩ := (mem_levelCoboundaries₂_iff _ _ _).1 hXcob

  let e : ↥((U).comap ℓ) →* ↥(Dq S F q σ) :=
    { toFun := fun h => ⟨ℓ h, h.2, Subgroup.mem_map.2
        ⟨primeLocalToGlobal (q : Nat.Primes) h, ⟨(show extArithLocalGroups S (Sum.inr q) from h.1), rfl⟩, rfl⟩⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun _ _ => Subtype.ext (by simp) }
  refine (mem_levelCoboundaries₂_iff _ _ _).2 ⟨ψD ∘ e,
    IsLevelConstant₁.precomp (rH := (Dq S F q σ).subtype) (rG := ℓ.comp ((U).comap ℓ).subtype) e (fun _ => rfl) hψDl, ?_⟩
  have hd := cochainsPullPush₂_d₁₂ (A := Rep.res (Subgroup.inclusion hDle) (ES S F)) (B := Rep.res (ℓ.subgroupComap (U)) (ES S F))
    e LinearMap.id (fun _ _ => rfl) ψD
  rw [hψDd] at hd
  exact hd.symm

end H4

section Main

variable (S : Finset Nat.Primes) (F : IntermediateField ℚ ℚb)

set_option hygiene false in
local notation "U" => IntermediateField.fixingSubgroup F

def vξ (ξ : ↥U × ↥U → SUn S F) : ↥U × ↥U → Additive ℚbˣ := fun g => galoisSUnitsToUnits S (ξ g)

lemma isGood_vξ (ξ : ↥(levelCocyclesSr₂ (U).subtype S (SUn S F))) : IsGood F (vξ S F ξ) := by
  obtain ⟨hc, hl⟩ := (mem_levelCocyclesSr₂_iff _ _ _ _).1 ξ.2
  refine ⟨(mem_cocycles₂_iff (A := Un (U)) _).2 fun g h j => ?_, ?_⟩
  · rw [mem_cocycles₂_iff] at hc
    have := congrArg (galoisSUnitsToUnits S) (hc g h j)
    rw [map_add, map_add] at this
    exact this
  · have := hl.isLevelConstant₂.comp (galoisSUnitsToUnits S)
    exact this

end Main

end P2MHasseP
p2m_reactivate "P2MW.S_groupCohomology_continuousH2Sr_galoisSUnitsRep_eq_zero_of_forall_res_extArithIndex_eq_zero.P2MHasseP"

end
p2m_reactivate "P2MW.S_groupCohomology_continuousH2Sr_galoisSUnitsRep_eq_zero_of_forall_res_extArithIndex_eq_zero.P2MHasseP"

open P2MHasseP in
theorem solution
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [IsGalois ℚ F] (hF : F.IsUnramifiedOutside S)
    (γ : ∀ v : extArithIndex S, (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ (F.fixingSubgroup ⊔ (extArithLoc S v).range) →
      (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (hγ : ∀ v t, (γ v t : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ (F.fixingSubgroup ⊔ (extArithLoc S v).range)) = t)
    (x : continuousH2Sr F.fixingSubgroup.subtype S (Rep.res F.fixingSubgroup.subtype (galoisSUnitsRep S)))
    (hx : (p : ℤ) • x = 0)
    (h : ∀ (v : extArithIndex S) (t : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ (F.fixingSubgroup ⊔ (extArithLoc S v).range)),
      continuousH2Map (rH := F.fixingSubgroup.subtype)
          (rG := (F.fixingSubgroup ⊓ ((extArithLoc S v).range.map (MulAut.conj (γ v t)).toMonoidHom)).subtype)
          (A := Rep.res F.fixingSubgroup.subtype (galoisSUnitsRep S))
          (B := Rep.res (F.fixingSubgroup ⊓ ((extArithLoc S v).range.map (MulAut.conj (γ v t)).toMonoidHom)).subtype
            (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)))
          (Subgroup.inclusion inf_le_left) (fun _ => rfl) (galoisSUnitsToUnits S) (fun _ _ => rfl)
          (continuousH2SrToContinuousH2 F.fixingSubgroup.subtype S (Rep.res F.fixingSubgroup.subtype (galoisSUnitsRep S)) x) = 0) :
    x = 0 := by
  obtain ⟨ξ, rfl⟩ := continuousH2Srπ_surjective _ _ _ x
  have hgood : IsGood F (vξ S F ξ) := isGood_vξ S F ξ

  have hcob : ∀ (v : extArithIndex S) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
      HasLocalCob F (vξ S F ξ) (F.fixingSubgroup ⊓ (extArithLoc S v).range.map (MulAut.conj σ).toMonoidHom) inf_le_left :=
    fun v => hasLocalCob_all F hgood _ (γ v) (hγ v) fun t =>
      (mem_levelCoboundaries₂_iff _ _ _).1 ((map_srTo_π_eq_zero_iff S _ _ _ _ ξ).1 (h v t))
  have hall : ∀ (q : ↥S) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
      continuousH2Map (rH := F.fixingSubgroup.subtype) (rG := (Dq S F q σ).subtype) (A := SUn S F) (B := Un (Dq S F q σ))
        (Subgroup.inclusion inf_le_left) (fun _ => rfl) (galoisSUnitsToUnits S) (fun _ _ => rfl)
        (continuousH2SrToContinuousH2 F.fixingSubgroup.subtype S (SUn S F) (continuousH2Srπ _ S _ ξ)) = 0 :=
    fun q σ => (map_srTo_π_eq_zero_iff S _ _ _ _ ξ).2 ((mem_levelCoboundaries₂_iff _ _ _).2 (hcob (Sum.inr q) σ))
  by_cases h4 : p = 2 → ∃ i ∈ F, i ^ 2 = -1
  · exact A_h4 S hpS F hF h4 _ hx hall

  push Not at h4
  obtain ⟨hp2, -⟩ := h4
  subst hp2
  obtain ⟨i, hi⟩ : ∃ i : AlgebraicClosure ℚ, i ^ 2 = -1 := IsAlgClosed.exists_pow_nat_eq (-1) two_pos
  set F' : IntermediateField ℚ (AlgebraicClosure ℚ) := F ⊔ IntermediateField.adjoin ℚ {i} with hF'def
  have h2S : (⟨2, Nat.prime_two⟩ : Nat.Primes) ∈ S := hpS
  have hF' : F'.IsUnramifiedOutside S := by
    refine hF.sup_adjoin_simple_of_pow_mem S Nat.prime_two h2S (α := i) ?_ ?_
    · rw [hi]; exact neg_mem (one_mem _)
    · intro A _
      rw [hi, inv_neg, inv_one]
      exact ⟨neg_mem A.one_mem, neg_mem A.one_mem⟩
  have hU'U : F'.fixingSubgroup ≤ F.fixingSubgroup := IntermediateField.fixingSubgroup_antitone le_sup_left
  have hiF' : i ∈ F' := (le_sup_right : IntermediateField.adjoin ℚ {i} ≤ F') (IntermediateField.mem_adjoin_simple_self ℚ i)

  have hall' : ∀ (q : ↥S) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
      continuousH2Map (rH := F'.fixingSubgroup.subtype) (rG := (Dq S F' q σ).subtype) (A := SUn S F') (B := Un (Dq S F' q σ))
        (Subgroup.inclusion inf_le_left) (fun _ => rfl) (galoisSUnitsToUnits S) (fun _ _ => rfl)
        (continuousH2SrToContinuousH2 F'.fixingSubgroup.subtype S (SUn S F')
          (continuousH2SrMap (rH := F.fixingSubgroup.subtype) (rG := F'.fixingSubgroup.subtype) (A := SUn S F) (B := SUn S F')
            (Subgroup.inclusion hU'U) (fun _ => rfl) S LinearMap.id (fun _ _ => rfl) (continuousH2Srπ _ S _ ξ))) = 0 :=
    fun q σ => (map_srTo_srMap_π_eq_zero_iff S _ _ _ _ _ _ _ _ ξ).2
      ((mem_levelCoboundaries₂_iff _ _ _).2 ((hcob (Sum.inr q) σ).mono (inf_le_inf_right _ hU'U)))
  have hres := A_h4 S hpS F' hF' (fun _ => ⟨i, hiF', hi⟩) _ (by rw [← map_zsmul, hx, map_zero]) hall'
  exact groupCohomology.continuousH2Sr_galoisSUnitsRep_eq_zero_of_res_adjoin_sqrt_neg_one_eq_zero S h2S F hF i hi γ hγ _ hx
    hres h

end S_groupCohomology_continuousH2Sr_galoisSUnitsRep_eq_zero_of_forall_res_extArithIndex_eq_zero
end P2MW
export P2MW.S_groupCohomology_continuousH2Sr_galoisSUnitsRep_eq_zero_of_forall_res_extArithIndex_eq_zero (solution)
