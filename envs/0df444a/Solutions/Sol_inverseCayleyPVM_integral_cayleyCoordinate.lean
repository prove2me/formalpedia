-- Prove2me | solution 1 for inverseCayleyPVM_integral_cayleyCoordinate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:04:28.886378+00:00
-- url     : https://prove2.me/submissions/0513f2d0-69e5-4070-9687-934a5055c7a7

import Definitions.Def_Spectral_Cayley_Inverse
import Definitions.Def_Spectral_PVM_Unbounded
import Definitions.Def_Spectral_Spectral_CayleyCalculus
import Definitions.Def_Spectral_Spectral_Polarization
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unitary
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Definitions.Def_Spectral_Spectral_Existence
import Theorems.Thm_integral_normalCfcScalarMeasure_complex
import Theorems.Thm_normalCfcPVM_scalarMeasure
import Theorems.Thm_normalCfcOperator_unitPole_eq_zero
import Theorems.Thm_PVM_inner_integral_self
import Theorems.Thm_PVM_simpleIntegral_one
import Theorems.Thm_PVM_simpleIntegral_zero
attribute [local simp] PVM.simpleIntegral_one
attribute [local simp] PVM.simpleIntegral_zero


section
open MeasureTheory
open CompactlySupported
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
private theorem inverseCayley_scalar_identity
    (U : E →L[ℂ] E) (hunit : U ∈ unitary (E →L[ℂ] E))
    (z : spectrum ℂ U) (hz : (z : ℂ) ≠ 1) :
    (1 - (z : ℂ)) * (inverseCayleyCoordinate z : ℂ) =
      Complex.I * (1 + (z : ℂ)) := by
  have hnorm : ‖(z : ℂ)‖ = 1 :=
    spectrum.norm_eq_one_of_unitary hunit z.property
  have hcircle : (z : ℂ).re * (z : ℂ).re +
      (z : ℂ).im * (z : ℂ).im = 1 := by
    calc
      (z : ℂ).re * (z : ℂ).re + (z : ℂ).im * (z : ℂ).im =
          Complex.normSq z := (Complex.normSq_apply z).symm
      _ = ‖(z : ℂ)‖ ^ 2 := Complex.normSq_eq_norm_sq z
      _ = 1 := by rw [hnorm, one_pow]
  have hden : 1 - (z : ℂ).re ≠ 0 := by
    intro hzero
    have hre : (z : ℂ).re = 1 := (sub_eq_zero.mp hzero).symm
    have him : (z : ℂ).im = 0 := by
      rw [hre, one_mul] at hcircle
      nlinarith only [hcircle, sq_nonneg (z : ℂ).im]
    apply hz
    apply Complex.ext
    · simpa only [Complex.one_re] using hre
    · simpa only [Complex.one_im] using him
  apply Complex.ext
  · change (((1 : ℂ) - (z : ℂ)) *
        ((-((z : ℂ).im) / (1 - (z : ℂ).re) : ℝ) : ℂ)).re =
      (Complex.I * (1 + (z : ℂ))).re
    simp only [Complex.mul_re, Complex.sub_re, Complex.one_re,
      Complex.ofReal_re, Complex.sub_im, Complex.one_im, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.add_re, Complex.add_im,
      zero_mul, one_mul, mul_zero, sub_zero, zero_sub]
    field_simp
    rw [zero_add]
  · change (((1 : ℂ) - (z : ℂ)) *
        ((-((z : ℂ).im) / (1 - (z : ℂ).re) : ℝ) : ℂ)).im =
      (Complex.I * (1 + (z : ℂ))).im
    simp only [Complex.mul_im, Complex.sub_re, Complex.one_re,
      Complex.ofReal_re, Complex.sub_im, Complex.one_im, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.add_re, Complex.add_im,
      zero_mul, one_mul, mul_zero, zero_sub, zero_add]
    field_simp
    nlinarith only [hcircle]
private theorem cayleyCoordinate_inverseCayleyCoordinate
    (U : E →L[ℂ] E) (hunit : U ∈ unitary (E →L[ℂ] E))
    (z : spectrum ℂ U) (hz : (z : ℂ) ≠ 1) :
    cayleyCoordinate (inverseCayleyCoordinate z) = (z : ℂ) := by
  have hden : (inverseCayleyCoordinate z : ℂ) + Complex.I ≠ 0 := by
    intro hzero
    have him := congrArg Complex.im hzero
    simp only [Complex.add_im, Complex.ofReal_im, Complex.I_im,
      zero_add, Complex.zero_im] at him
    exact one_ne_zero him
  rw [cayleyCoordinate, div_eq_iff hden]
  linear_combination inverseCayley_scalar_identity U hunit z hz
private theorem normalCfcScalarMeasure_unitPole_eq_zero
    (U : E →L[ℂ] E) (hU : IsStarNormal U)
    (hNoFixed : ∀ x, U x = x → x = 0) (x : E) :
    normalCfcScalarMeasure U hU x (unitPole U) = 0 := by
  have hreal : (normalCfcScalarMeasure U hU x).real (unitPole U) = 0 := by
    have hinner := inner_normalCfcOperator_self U hU (unitPole U) x
    rw [normalCfcOperator_unitPole_eq_zero U hU hNoFixed,
      zero_apply, inner_zero_left] at hinner
    exact_mod_cast hinner.symm
  exact (measureReal_eq_zero_iff
    (measure_ne_top (normalCfcScalarMeasure U hU x) (unitPole U))).mp hreal
omit [CompleteSpace E] in
private theorem continuousLinearMap_eq_of_inner_self_eq_right
    (T S : E →L[ℂ] E)
    (h : ∀ x : E, @inner ℂ E _ x (T x) = @inner ℂ E _ x (S x)) :
    T = S := by
  apply continuousLinearMap_eq_of_inner_self_eq
  intro x
  rw [← inner_conj_symm (T x) x, ← inner_conj_symm (S x) x, h]
end

set_option autoImplicit false
open MeasureTheory
open CompactlySupported
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution
    (U : E →L[ℂ] E) (hU : IsStarNormal U)
    (hunit : U ∈ unitary (E →L[ℂ] E))
    (hNoFixed : ∀ x, U x = x → x = 0) :
    (inverseCayleyPVM U hU).integral cayleyCoordinate
      cayleyCoordinate_measurable cayleyCoordinate_bounded = U := by
  apply continuousLinearMap_eq_of_inner_self_eq_right
  intro x
  let mu := normalCfcScalarMeasure U hU x
  let coord : C(spectrum ℂ U, ℂ) :=
    (ContinuousMap.id ℂ).restrict (spectrum ℂ U)
  have hpole : mu (unitPole U) = 0 :=
    normalCfcScalarMeasure_unitPole_eq_zero U hU hNoFixed x
  have hae : ∀ᵐ z ∂mu, z ∉ unitPole U := by
    apply ae_iff.mpr
    rw [show {z : spectrum ℂ U | ¬z ∉ unitPole U} = unitPole U by
      ext z
      simp only [Set.mem_ofPred_eq, not_not]]
    exact hpole
  calc
    @inner ℂ E _ x
        ((inverseCayleyPVM U hU).integral cayleyCoordinate
          cayleyCoordinate_measurable cayleyCoordinate_bounded x) =
        ∫ t, cayleyCoordinate t ∂((inverseCayleyPVM U hU).scalarMeasure x) :=
      PVM.inner_integral_self _ _ _ _ x
    _ = ∫ t, cayleyCoordinate t ∂Measure.map
        (fun z : spectrum ℂ U => inverseCayleyCoordinate z) mu := by
      rw [inverseCayleyPVM, normalCfcPVM_scalarMeasure]
    _ = ∫ z, cayleyCoordinate (inverseCayleyCoordinate z) ∂mu := by
      have hgEq : (fun z : spectrum ℂ U => inverseCayleyCoordinate z) =
          inverseCayleyCoordinate ∘ Subtype.val := by
        funext z
        rfl
      rw [hgEq]
      exact integral_map
        (inverseCayleyCoordinate_measurable.comp
          measurable_subtype_coe).aemeasurable
        cayleyCoordinate_measurable.aestronglyMeasurable
    _ = ∫ z, (z : ℂ) ∂mu := by
      apply integral_congr_ae
      filter_upwards [hae] with z hz
      exact cayleyCoordinate_inverseCayleyCoordinate U hunit z hz
    _ = @inner ℂ E _ x ((cfcHom hU) coord x) := by
      exact integral_normalCfcScalarMeasure_complex U hU x coord
    _ = @inner ℂ E _ x (U x) := by
      rw [cfcHom_id]
