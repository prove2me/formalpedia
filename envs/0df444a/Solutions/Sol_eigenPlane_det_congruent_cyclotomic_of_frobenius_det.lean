-- Prove2me | solution 1 for eigenPlane_det_congruent_cyclotomic_of_frobenius_det
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/a711e8ca-8f16-5118-b199-bc1928d382f4

import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Integer
import Mathlib.RingTheory.Flat.Basic
import Mathlib.Algebra.Module.Submodule.Pointwise
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Tactic.Push
import Mathlib.Tactic.Module
import Definitions.Def_ModularCurve_EichlerShimuraData
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_Adic
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Theorems.Thm_GaloisRepAdic_detIsCyclotomic_of_forall_frobenius_det_eq
import Theorems.Thm_W54_finite_free_tateModule
import Theorems.Thm_ModularCurve_JZero_finite_torsion_pow_of_cardinalityAJ
import Theorems.Thm_ModularCurve_JZero_cardinalityAJ_genusFF
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_eigenPlane_det_congruent_cyclotomic_of_frobenius_det
p2m_attr_erase "instance" "FrobeniusDensity.isMaximal_ratPrimeIdeal FrobeniusDensity.liesOver_ratBelow AlgebraicClosure.Rat.isGalois AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC"
p2m_attr_erase "instance" "AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC AlgebraicCurve.CellDissection.decEqE ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.instIsDomainTensorProduct ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring"
p2m_attr_erase "simp" "ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.abelJacobiDiv_single AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply"
p2m_attr_erase "simp" "ModularCurve.baseChangeHom_tmul ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar HahnSeries.ramScale_apply"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open ModularCurve AlgebraicCurve IsLocalRing TensorProduct Pointwise

local notation "Qbar" => AlgebraicClosure ℚ

namespace ArDetSol

section Generic

variable (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable (K : Type) [Field K] [Algebra A K] [IsFractionRing A K]
variable (V : Type) [AddCommGroup V] [Module A V] [Module.Free A V] [Module.Finite A V]

noncomputable def ψ : V →ₗ[A] (K ⊗[A] V) := TensorProduct.mk A K V 1

omit [IsDomain A] [IsDiscreteValuationRing A] [IsFractionRing A K]
  [Module.Free A V] [Module.Finite A V] in
theorem ψ_apply (x : V) : ψ A K V x = (1 : K) ⊗ₜ[A] x := rfl

omit [IsDomain A] [IsDiscreteValuationRing A] [Module.Finite A V] in
theorem ψ_injective : Function.Injective (ψ A K V) := by
  have halg : Function.Injective (Algebra.linearMap A K) := IsFractionRing.injective A K
  have hr : Function.Injective ((Algebra.linearMap A K).rTensor V) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ halg
  intro x y hxy
  have hcomp : ∀ z : V,
      ψ A K V z = (Algebra.linearMap A K).rTensor V ((TensorProduct.lid A V).symm z) := by
    intro z
    simp [ψ_apply, TensorProduct.lid_symm_apply, LinearMap.rTensor_tmul,
      Algebra.linearMap_apply, map_one]
  rw [hcomp, hcomp] at hxy
  exact (TensorProduct.lid A V).symm.injective (hr hxy)

omit [IsDomain A] [IsDiscreteValuationRing A] [Module.Free A V] [Module.Finite A V] in
theorem clear_denominator (z : K ⊗[A] V) :
    ∃ s : nonZeroDivisors A, ∃ m : V, (s : A) • z = ψ A K V m := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨1, 0, by simp⟩
  | tmul c m =>
    obtain ⟨⟨c', s⟩, hcs⟩ := IsLocalization.surj (nonZeroDivisors A) c
    refine ⟨s, c' • m, ?_⟩
    have h1 : (s : A) • c = algebraMap A K c' := by
      rw [Algebra.smul_def, mul_comm]
      exact hcs
    rw [ψ_apply, TensorProduct.smul_tmul', h1, ← TensorProduct.smul_tmul]
    congr 1
    rw [Algebra.smul_def, mul_one]
  | add x y hx hy =>
    obtain ⟨sx, mx, hmx⟩ := hx
    obtain ⟨sy, my, hmy⟩ := hy
    refine ⟨sx * sy, (sy : A) • mx + (sx : A) • my, ?_⟩
    have hco : ((sx * sy : nonZeroDivisors A) : A) = (sx : A) * (sy : A) := rfl
    rw [map_add, map_smul, map_smul, ← hmx, ← hmy, hco, smul_add]
    module

variable (W : Submodule K (K ⊗[A] V))

noncomputable def L : Submodule A V := (W.restrictScalars A).comap (ψ A K V)

omit [IsDomain A] [IsDiscreteValuationRing A] [IsFractionRing A K]
  [Module.Free A V] [Module.Finite A V] in
theorem mem_L {x : V} : x ∈ L A K V W ↔ (1 : K) ⊗ₜ[A] x ∈ W := Iff.rfl

omit [IsDomain A] [IsDiscreteValuationRing A] [IsFractionRing A K]
  [Module.Free A V] [Module.Finite A V] in
theorem L_stable (f : Module.End A V) (hf : ∀ w ∈ W, f.baseChange K w ∈ W) :
    ∀ x ∈ L A K V W, f x ∈ L A K V W := by
  intro x hx
  rw [mem_L]
  have h : (1 : K) ⊗ₜ[A] f x = f.baseChange K ((1 : K) ⊗ₜ[A] x) := by
    rw [LinearMap.baseChange_tmul]
  rw [h]
  exact hf _ hx

omit [IsDomain A] [IsDiscreteValuationRing A] [Module.Free A V] [Module.Finite A V] in
theorem L_saturated (d : A) (hd : d ≠ 0) (x : V) (hdx : d • x ∈ L A K V W) :
    x ∈ L A K V W := by
  rw [mem_L] at hdx ⊢
  have hKd : (algebraMap A K d) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr hd
  have h : (1 : K) ⊗ₜ[A] (d • x) = algebraMap A K d • ((1 : K) ⊗ₜ[A] x) := by
    rw [TensorProduct.smul_tmul', ← TensorProduct.smul_tmul]
    congr 1
    rw [Algebra.smul_def, mul_one, smul_eq_mul, mul_one]
  rw [h] at hdx
  have h2 := W.smul_mem (algebraMap A K d)⁻¹ hdx
  rwa [inv_smul_smul₀ hKd] at h2

set_option maxSynthPendingDepth 3 in
set_option maxHeartbeats 8000000 in

theorem exists_matched_bases (hW2 : Module.finrank K ↥W = 2) :
    ∃ (bL : Module.Basis (Fin 2) A ↥(L A K V W)) (bW : Module.Basis (Fin 2) K ↥W),
      ∀ i, (bW i : K ⊗[A] V) = ψ A K V (bL i : V) := by
  classical
  obtain ⟨n, bL0⟩ := (L A K V W).basisOfPid (Module.Free.chooseBasis A V)
  set fam0 : Fin n → K ⊗[A] V := fun i => ψ A K V (bL0 i : V) with hfam0

  have hind0 : LinearIndependent K fam0 := by
    rw [linearIndependent_iff']
    intro t c hc i hit
    obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors A) t c
    have hbK : (algebraMap A K (b : A)) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr
        (mem_nonZeroDivisors_iff_ne_zero.mp b.2)
    have hd : ∀ j ∈ t, ∃ dj : A, algebraMap A K dj = (b : A) • c j := by
      intro j hj
      exact (hb j hj)
    choose! d hdd using hd
    have hrel : (∑ j ∈ t, d j • (bL0 j : V)) = 0 := by
      apply ψ_injective A K V
      rw [map_sum, map_zero]
      have h1 : ∀ j ∈ t, ψ A K V (d j • (bL0 j : V)) = (b : A) • (c j • fam0 j) := by
        intro j hj
        rw [map_smul]
        conv_lhs => rw [← algebraMap_smul (A := K) (d j)]
        rw [hdd j hj, smul_assoc]
      rw [Finset.sum_congr rfl h1, ← Finset.smul_sum, hc, smul_zero]
    have hsub : (∑ j ∈ t, d j • bL0 j) = (0 : ↥(L A K V W)) := by
      apply Subtype.ext
      push_cast
      exact hrel
    have hz := linearIndependent_iff'.mp bL0.linearIndependent t d hsub i hit
    have h2 : algebraMap A K (d i) = (b : A) • c i := hdd i hit
    rw [hz, map_zero] at h2
    rw [Algebra.smul_def] at h2
    rcases mul_eq_zero.mp h2.symm with h | h
    · exact absurd h hbK
    · exact h

  have hspan0 : Submodule.span K (Set.range fam0) = W := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact (bL0 i).2
    · intro w hw
      obtain ⟨sd, m, hsm⟩ := clear_denominator A K V w
      have hmL : m ∈ L A K V W := by
        rw [mem_L, ← ψ_apply, ← hsm]
        exact Submodule.smul_of_tower_mem W (sd : A) hw
      have hsK : (algebraMap A K (sd : A)) ≠ 0 :=
        (map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr
          (mem_nonZeroDivisors_iff_ne_zero.mp sd.2)
      have hmrepr := (bL0.sum_repr ⟨m, hmL⟩).symm
      have hcoe : m = ∑ j, bL0.repr ⟨m, hmL⟩ j • (bL0 j : V) := by
        have h5 := congrArg (Subtype.val) hmrepr
        push_cast at h5
        exact h5
      have hψm : ψ A K V m =
          ∑ j, algebraMap A K (bL0.repr ⟨m, hmL⟩ j) • fam0 j := by
        conv_lhs => rw [hcoe]
        rw [map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_smul]
        conv_lhs => rw [← algebraMap_smul (A := K) (bL0.repr ⟨m, hmL⟩ j)]
      have hw2 : w = (algebraMap A K (sd : A))⁻¹ • ψ A K V m := by
        rw [← hsm]
        conv_rhs => rw [← algebraMap_smul (A := K) (sd : A) w]
        rw [← mul_smul, inv_mul_cancel₀ hsK, one_smul]
      rw [hw2, hψm, Finset.smul_sum]
      apply Submodule.sum_mem
      intro j _
      rw [smul_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

  have hn : n = 2 := by
    have hfr := finrank_span_eq_card hind0
    rw [hspan0, hW2] at hfr
    simpa using hfr.symm
  subst hn

  have hmemW : ∀ i, fam0 i ∈ W := fun i => (bL0 i).2
  set fam' : Fin 2 → ↥W := fun i => ⟨fam0 i, hmemW i⟩ with hfam'
  have hind' : LinearIndependent K fam' := by
    have hcomp : fam0 = (W.subtype) ∘ fam' := by
      funext i; rfl
    rw [hcomp] at hind0
    exact LinearIndependent.of_comp _ hind0
  have hspan' : ⊤ ≤ Submodule.span K (Set.range fam') := by
    intro x _
    have hx : (x : K ⊗[A] V) ∈ Submodule.span K (Set.range fam0) := by
      rw [hspan0]
      exact x.2
    have hmap : Submodule.span K (Set.range fam0) =
        Submodule.map (W.subtype) (Submodule.span K (Set.range fam')) := by
      rw [Submodule.map_span]
      congr 1
      rw [← Set.range_comp]
      rfl
    rw [hmap] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have h6 : y = x := Subtype.ext hyx
    rwa [← h6]
  refine ⟨bL0, Module.Basis.mk hind' hspan', fun i => ?_⟩
  rw [Module.Basis.mk_apply]

omit [IsDomain A] [IsDiscreteValuationRing A] [IsFractionRing A K]
  [Module.Free A V] [Module.Finite A V] in
set_option maxSynthPendingDepth 3 in
set_option maxHeartbeats 8000000 in

theorem det_bridge
    (bL : Module.Basis (Fin 2) A ↥(L A K V W))
    (bW : Module.Basis (Fin 2) K ↥W)
    (hmatch : ∀ i, (bW i : K ⊗[A] V) = ψ A K V (bL i : V))
    (f : Module.End A V)
    (hfL : ∀ x ∈ L A K V W, f x ∈ L A K V W)
    (hfW : ∀ w ∈ W, f.baseChange K w ∈ W) :
    algebraMap A K (LinearMap.det (f.restrict hfL)) =
      LinearMap.det (((f.baseChange K).restrict hfW : ↥W →ₗ[K] ↥W)) := by
  classical
  set Amat := LinearMap.toMatrix bL bL (f.restrict hfL) with hA
  have hmat : LinearMap.toMatrix bW bW
      (((f.baseChange K).restrict hfW : ↥W →ₗ[K] ↥W)) =
      (algebraMap A K).mapMatrix Amat := by
    apply Matrix.ext
    intro i j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, LinearMap.toMatrix_apply]
    have hcoeval : (((f.baseChange K).restrict hfW) (bW j) : K ⊗[A] V) =
        ∑ i', algebraMap A K (Amat i' j) • (bW i' : K ⊗[A] V) := by
      have h0 : (((f.baseChange K).restrict hfW) (bW j) : K ⊗[A] V) =
          f.baseChange K (bW j : K ⊗[A] V) := rfl
      rw [h0, hmatch j, ψ_apply, LinearMap.baseChange_tmul]
      have hfrepr : f (bL j : V) = ∑ i', Amat i' j • (bL i' : V) := by
        have h1 : (f.restrict hfL) (bL j) = ∑ i', Amat i' j • bL i' := by
          have h2 := (bL.sum_repr ((f.restrict hfL) (bL j))).symm
          rw [h2]
          refine Finset.sum_congr rfl fun i' _ => ?_
          rw [hA, LinearMap.toMatrix_apply]
        have h3 := congrArg (Subtype.val) h1
        push_cast at h3
        exact h3
      rw [show f (bL j : V) = ∑ i', Amat i' j • (bL i' : V) from hfrepr]
      rw [tmul_sum]
      refine Finset.sum_congr rfl fun i' _ => ?_
      rw [hmatch i', ψ_apply, TensorProduct.tmul_smul, algebraMap_smul (A := K)]
    have hval : ((f.baseChange K).restrict hfW) (bW j) =
        ∑ i', algebraMap A K (Amat i' j) • bW i' := by
      apply Subtype.ext
      rw [hcoeval]
      push_cast
      rfl
    rw [hval]
    have hrepr := Module.Basis.repr_sum_self bW (fun i' => algebraMap A K (Amat i' j))
    exact congrFun hrepr i
  symm
  calc LinearMap.det (((f.baseChange K).restrict hfW : ↥W →ₗ[K] ↥W))
      = ((algebraMap A K).mapMatrix Amat).det := by
        rw [← LinearMap.det_toMatrix bW, hmat]
    _ = algebraMap A K Amat.det := (RingHom.map_det _ _).symm
    _ = algebraMap A K (LinearMap.det (f.restrict hfL)) := by
        rw [hA, LinearMap.det_toMatrix]

end Generic

section Carrier

variable {M : ℕ} [NeZero M] (lam : ℕ) [Fact lam.Prime]
variable (O'' : Type) [CommRing O''] [IsDomain O''] [IsDiscreteValuationRing O'']
  [IsAdicComplete (maximalIdeal O'') O''] [Finite (ResidueField O'')]
  [CharZero O''] [Algebra ℤ_[lam] O'']
  [Module HeckeAlg (JZero M)] [Module ℤ_[lam] (TateModule lam (JZero M))]

omit [Module HeckeAlg (JZero M)] [Module ℤ_[lam] (TateModule lam (JZero M))] in

theorem hfin_jzero : Set.Finite {v : JZero M | lam • v = 0} := by
  have h1 : Finite (Pic0.torsion Qbar (modularFunctionFieldBar M) (lam ^ 1)) :=
    ModularCurve.JZero.finite_torsion_pow_of_cardinalityAJ M lam
      (ModularCurve.JZero.cardinalityAJ_genusFF M lam) 1
  rw [pow_one] at h1
  have hset : {v : JZero M | lam • v = 0} =
      ((Pic0.torsion Qbar (modularFunctionFieldBar M) lam :
        AddSubgroup (JZero M)) : Set (JZero M)) := by
    ext v
    simp only [Set.mem_setOf_eq, SetLike.mem_coe, Pic0.mem_torsion, natCast_zsmul]
  rw [hset]
  exact Set.toFinite _

omit [IsAdicComplete (maximalIdeal O'') O''] [CharZero O''] in

theorem lam_mem_maximalIdeal : (lam : O'') ∈ maximalIdeal O'' := by
  set ψk : ℤ_[lam] →+* ResidueField O'' :=
    (IsLocalRing.residue O'').comp (algebraMap ℤ_[lam] O'') with hψk
  have hker : RingHom.ker ψk ≠ ⊥ := by
    intro h0
    have hinj : Function.Injective ψk := by
      rwa [RingHom.injective_iff_ker_eq_bot]
    have : Finite ℤ_[lam] := Finite.of_injective ψk hinj
    exact absurd this (inferInstance : Infinite ℤ_[lam]).not_finite
  obtain ⟨k, hk⟩ := PadicInt.ideal_eq_span_pow_p hker
  have hkne : k ≠ 0 := by
    intro h0
    rw [h0, pow_zero] at hk
    have h1 : (1 : ℤ_[lam]) ∈ RingHom.ker ψk := by
      rw [hk]; exact Ideal.mem_span_singleton_self 1
    rw [RingHom.mem_ker, map_one] at h1
    exact one_ne_zero h1
  have hmem : ((lam : ℤ_[lam]) ^ k) ∈ RingHom.ker ψk := by
    rw [hk]; exact Ideal.mem_span_singleton_self _
  rw [RingHom.mem_ker, map_pow] at hmem
  have hres : ψk (lam : ℤ_[lam]) = 0 := pow_eq_zero_iff hkne |>.mp hmem
  have hres2 : IsLocalRing.residue O'' ((lam : O'')) = 0 := by
    have halg : algebraMap ℤ_[lam] O'' (lam : ℤ_[lam]) = (lam : O'') := by
      simp [map_natCast]
    rw [hψk] at hres
    simpa [RingHom.comp_apply, halg] using hres
  exact Ideal.Quotient.eq_zero_iff_mem.mp hres2

end Carrier

section Package

variable (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable (K : Type) [Field K] [Algebra A K] [IsFractionRing A K]
variable (V : Type) [AddCommGroup V] [Module A V] [Module.Free A V] [Module.Finite A V]
variable (W : Submodule K (K ⊗[A] V))
variable (ρM : (Qbar ≃ₐ[ℚ] Qbar) →* Module.End A V)
variable (hW : ∀ σ : Qbar ≃ₐ[ℚ] Qbar, ∀ w ∈ W, (ρM σ).baseChange K w ∈ W)

noncomputable def ρL : (Qbar ≃ₐ[ℚ] Qbar) →* Module.End A ↥(L A K V W) where
  toFun σ := (ρM σ).restrict (fun x hx => L_stable A K V W (ρM σ) (hW σ) x hx)
  map_one' := by
    ext x
    show (ρM 1) (x : V) = (x : V)
    rw [map_one]
    rfl
  map_mul' σ τ := by
    ext x
    show (ρM (σ * τ)) (x : V) = (ρM σ) ((ρM τ) (x : V))
    rw [map_mul]
    rfl

omit [Module.Free A V] [Module.Finite A V] in
set_option maxSynthPendingDepth 3 in

theorem ρL_continuous (hcont : GaloisActionIsAdicContinuous A ρM) :
    GaloisActionIsAdicContinuous A (ρL A K V W ρM hW) := by
  intro n
  obtain ⟨Lf, hLffin, hLfact⟩ := hcont n
  refine ⟨Lf, hLffin, ?_⟩
  intro σ hσ v
  have hx := hLfact σ hσ (v : V)
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow,
    Submodule.ideal_span_singleton_smul] at hx
  obtain ⟨y, -, hy⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hx
  have hπn : (π ^ n : A) ≠ 0 := pow_ne_zero n hπ.ne_zero
  have hxL : ρM σ (v : V) - (v : V) ∈ L A K V W :=
    Submodule.sub_mem _ (L_stable A K V W (ρM σ) (hW σ) _ v.2) v.2
  have hyL : y ∈ L A K V W :=
    L_saturated A K V W (π ^ n) hπn y (by rw [hy]; exact hxL)
  have hgoal : (ρL A K V W ρM hW) σ v - v = (π ^ n) • (⟨y, hyL⟩ : ↥(L A K V W)) := by
    apply Subtype.ext
    push_cast
    show ρM σ (v : V) - (v : V) = π ^ n • y
    exact hy.symm
  rw [hgoal, hπ.maximalIdeal_eq, Ideal.span_singleton_pow,
    Submodule.ideal_span_singleton_smul]
  exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top

set_option maxSynthPendingDepth 3 in

noncomputable def packaged (hW2 : Module.finrank K ↥W = 2)
    (hcont : GaloisActionIsAdicContinuous A ρM) : GaloisRepAdic A where
  V := ↥(L A K V W)
  instFree := Module.Free.of_basis (exists_matched_bases A K V W hW2).choose
  instFinite := Module.Finite.of_basis (exists_matched_bases A K V W hW2).choose
  finrank_eq := by
    rw [Module.finrank_eq_card_basis (exists_matched_bases A K V W hW2).choose]
    simp
  ρ := ρL A K V W ρM hW
  isAdicContinuous := ρL_continuous A K V W ρM hW hcont

set_option maxSynthPendingDepth 3 in
set_option maxHeartbeats 8000000 in

theorem det_congruent_package (hW2 : Module.finrank K ↥W = 2)
    (hcont : GaloisActionIsAdicContinuous A ρM)
    {p : ℕ} (hp : p.Prime) (hpA : (p : A) ∈ maximalIdeal A)
    (S' : Finset ℕ)
    (hdet : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S' → ∀ B : ValuationSubring Qbar,
      B.LiesOverPrime ℓ → ∀ τ : Qbar ≃ₐ[ℚ] Qbar, B.IsFrobeniusAt τ ℓ →
        LinearMap.det (((ρM τ).baseChange K).restrict (hW τ) : ↥W →ₗ[K] ↥W) = (ℓ : K)) :
    ∀ (σ : Qbar ≃ₐ[ℚ] Qbar) (n a : ℕ),
      (∀ μ : Qbar, μ ^ p ^ n = 1 → σ μ = μ ^ a) →
      ∃ d : A, algebraMap A K d =
          LinearMap.det (((ρM σ).baseChange K).restrict (hW σ) : ↥W →ₗ[K] ↥W) ∧
        d - (a : A) ∈ Ideal.span {((p ^ n : ℕ) : A)} := by
  classical
  obtain ⟨bL, bW, hmatch⟩ := exists_matched_bases A K V W hW2
  have hbridge : ∀ σ : Qbar ≃ₐ[ℚ] Qbar,
      algebraMap A K (LinearMap.det
        ((ρM σ).restrict (fun x hx => L_stable A K V W (ρM σ) (hW σ) x hx))) =
        LinearMap.det (((ρM σ).baseChange K).restrict (hW σ) : ↥W →ₗ[K] ↥W) :=
    fun σ => det_bridge A K V W bL bW hmatch (ρM σ) _ (hW σ)
  have hengine := GaloisRepAdic.detIsCyclotomic_of_forall_frobenius_det_eq
    (packaged A K V W ρM hW hW2 hcont) hp hpA S' (by
      intro ℓ hℓ hℓS B τ hB hτ
      have h1 := hdet ℓ hℓ hℓS B hB τ hτ
      rw [← hbridge τ] at h1
      have h2 : algebraMap A K (LinearMap.det
          ((ρM τ).restrict (fun x hx => L_stable A K V W (ρM τ) (hW τ) x hx))) =
          algebraMap A K ((ℓ : A)) := by
        rw [h1, map_natCast]
      exact (IsFractionRing.injective A K) h2)
  intro σ n a hpow
  refine ⟨LinearMap.det ((packaged A K V W ρM hW hW2 hcont).ρ σ), ?_, hengine.2 n σ a hpow⟩
  exact hbridge σ

end Package

end ArDetSol

open ArDetSol in
set_option maxSynthPendingDepth 3 in
set_option maxHeartbeats 8000000 in
theorem solution
    {M : ℕ} [NeZero M] (lam : ℕ) [Fact lam.Prime]
    (O'' : Type) [CommRing O''] [IsDomain O''] [IsDiscreteValuationRing O'']
  [IsAdicComplete (maximalIdeal O'') O''] [Finite (ResidueField O'')]
  [CharZero O''] [Algebra ℤ_[lam] O'']
  (K : Type) [Field K] [Algebra O'' K] [IsFractionRing O'' K]
    [Module HeckeAlg (JZero M)] [Module ℤ_[lam] (TateModule lam (JZero M))]
      (_hsmul : ∀ (a : ℤ_[lam]) (x : TateModule lam (JZero M)) (n : ℕ),
        ((a • x : TateModule lam (JZero M)) : ℕ → JZero M) n =
          (PadicInt.toZModPow n a).val • (x : ℕ → JZero M) n)
    (S : Finset ℕ)
    (ρM : (Qbar ≃ₐ[ℚ] Qbar) →* Module.End O'' (O'' ⊗[ℤ_[lam]] TateModule lam (JZero M)))
    (hρ : ∀ (σ : Qbar ≃ₐ[ℚ] Qbar) (x y : TateModule lam (JZero M)),
      (y : ℕ → JZero M) = σ • (x : ℕ → JZero M) →
        ∀ b : O'', ρM σ (b ⊗ₜ[ℤ_[lam]] x) = b ⊗ₜ[ℤ_[lam]] y)
    (hcont : GaloisActionIsAdicContinuous O'' ρM)
    (W : Submodule K (K ⊗[O''] (O'' ⊗[ℤ_[lam]] TateModule lam (JZero M))))
    (hW2 : Module.finrank K W = 2)
    (hW : ∀ σ : Qbar ≃ₐ[ℚ] Qbar, ∀ w ∈ W, (ρM σ).baseChange K w ∈ W)
    (hfrobdet : ∀ (ℓ : ℕ), ℓ.Prime → ¬ ℓ ∣ M → ℓ ∉ S →
      ∀ B : ValuationSubring Qbar, B.LiesOverPrime ℓ →
        ∀ σ : Qbar ≃ₐ[ℚ] Qbar, B.IsFrobeniusAt σ ℓ →
          LinearMap.det (M := ↥W) (((ρM σ).baseChange K).restrict (hW σ)) = (ℓ : K)) :
    ∀ (σ : Qbar ≃ₐ[ℚ] Qbar) (n a : ℕ),
      (∀ μ : Qbar, μ ^ lam ^ n = 1 → σ μ = μ ^ a) →
      ∃ d : O'', algebraMap O'' K d =
          LinearMap.det (M := ↥W) (((ρM σ).baseChange K).restrict (hW σ)) ∧
        d - (a : O'') ∈ Ideal.span {((lam ^ n : ℕ) : O'')} := by
  classical
  have _ := hρ
  have hTff := W54.finite_free_tateModule (J := JZero M) (p := lam) _hsmul
    (hfin_jzero (M := M) lam)
  obtain ⟨hTfin, hTfree⟩ := hTff
  haveI := hTfin
  haveI := hTfree
  have hdet' : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S ∪ M.primeFactors →
      ∀ B : ValuationSubring Qbar, B.LiesOverPrime ℓ →
        ∀ τ : Qbar ≃ₐ[ℚ] Qbar, B.IsFrobeniusAt τ ℓ →
          LinearMap.det (((ρM τ).baseChange K).restrict (hW τ) : ↥W →ₗ[K] ↥W) = (ℓ : K) := by
    intro ℓ hℓ hℓS B hB τ hτ
    rw [Finset.mem_union, not_or] at hℓS
    refine hfrobdet ℓ hℓ ?_ hℓS.1 B hB τ hτ
    intro hdvd
    exact hℓS.2 (Nat.mem_primeFactors.mpr ⟨hℓ, hdvd, NeZero.ne M⟩)
  exact det_congruent_package O'' K (O'' ⊗[ℤ_[lam]] TateModule lam (JZero M)) W ρM hW hW2
    hcont (Fact.out) (lam_mem_maximalIdeal lam O'') (S ∪ M.primeFactors) hdet'

end S_eigenPlane_det_congruent_cyclotomic_of_frobenius_det
end P2MW
export P2MW.S_eigenPlane_det_congruent_cyclotomic_of_frobenius_det (solution)
