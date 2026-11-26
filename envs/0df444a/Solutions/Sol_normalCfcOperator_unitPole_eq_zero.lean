-- Prove2me | solution 1 for normalCfcOperator_unitPole_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:03:11.205643+00:00
-- url     : https://prove2.me/submissions/d1c8656a-3443-4347-9338-eb6245f5bd30

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
import Theorems.Thm_PVM_simpleIntegral_one
import Theorems.Thm_PVM_simpleIntegral_zero
attribute [local simp] PVM.simpleIntegral_one
attribute [local simp] PVM.simpleIntegral_zero


section
open MeasureTheory
open CompactlySupported
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
omit [CompleteSpace E] in
private theorem unitPole_measurable (U : E →L[ℂ] E) :
    MeasurableSet (unitPole U) := by
  exact measurableSet_singleton (1 : ℂ) |>.preimage measurable_subtype_coe
private theorem distanceToOneSq_ofReal (U : E →L[ℂ] E)
    (z : spectrum ℂ U) :
    ((distanceToOneSq U z : ℝ) : ℂ) = distanceToOneSqComplex U z := by
  change ((‖(z : ℂ) - 1‖ ^ 2 : ℝ) : ℂ) =
    star ((z : ℂ) - 1) * ((z : ℂ) - 1)
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
    Complex.normSq_eq_norm_sq]
private theorem cfcHom_distanceToOneSqComplex
    (U : E →L[ℂ] E) (hU : IsStarNormal U) :
    (cfcHom hU) (distanceToOneSqComplex U) = star (U - 1) * (U - 1) := by
  unfold distanceToOneSqComplex
  rw [map_mul, map_star, map_sub, map_one, cfcHom_id]
end

set_option autoImplicit false
open MeasureTheory
open CompactlySupported
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution
    (U : E →L[ℂ] E) (hU : IsStarNormal U)
    (hNoFixed : ∀ x, U x = x → x = 0) :
    normalCfcOperator U hU (unitPole U) = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  let P := normalCfcOperator U hU (unitPole U)
  let Q := normalCfcOperator U hU (unitPole U)ᶜ
  let y := P x
  have hQP : Q * P = 0 := by
    have hinter := normalCfcOperator_inter U hU (unitPole U)ᶜ (unitPole U)
      (unitPole_measurable U).compl (unitPole_measurable U)
    rw [Set.compl_inter_self, normalCfcOperator_empty] at hinter
    exact hinter.symm
  have hQy : Q y = 0 := by
    have happ := congrArg (fun T : E →L[ℂ] E => T x) hQP
    simpa only [mul_apply_eq_comp, zero_apply, y] using happ
  let mu := normalCfcScalarMeasure U hU y
  have hmuComplReal : mu.real (unitPole U)ᶜ = 0 := by
    have hinner := inner_normalCfcOperator_self U hU (unitPole U)ᶜ y
    change @inner ℂ E _ (Q y) y = (mu.real (unitPole U)ᶜ : ℂ) at hinner
    rw [hQy, inner_zero_left] at hinner
    exact_mod_cast hinner.symm
  have hmuCompl : mu (unitPole U)ᶜ = 0 := by
    rw [Measure.real, ENNReal.toReal_eq_zero_iff] at hmuComplReal
    exact hmuComplReal.resolve_right (measure_ne_top mu (unitPole U)ᶜ)
  have haePole : ∀ᵐ z ∂mu, z ∈ unitPole U := by
    exact mem_ae_iff.mpr hmuCompl
  have hzeroAE : (fun z => distanceToOneSq U z) =ᵐ[mu] 0 := by
    filter_upwards [haePole] with z hz
    change ‖(z : ℂ) - 1‖ ^ 2 = 0
    rw [show (z : ℂ) = 1 from hz, sub_self, norm_zero,
      zero_pow (by omega)]
  have hintegral : ∫ z, distanceToOneSq U z ∂mu = 0 :=
    integral_eq_zero_of_ae hzeroAE
  have hrepr :
      ∫ z, distanceToOneSq U z ∂mu =
        (@inner ℂ E _ y
          ((cfcHom hU) (distanceToOneSqComplex U) y)).re := by
    rw [integral_normalCfcScalarMeasure]
    congr 1
    congr 1
    apply congrArg (fun f : C(spectrum ℂ U, ℂ) => (cfcHom hU) f y)
    ext z
    exact distanceToOneSq_ofReal U z
  have hnormSq : ‖(U - 1) y‖ ^ 2 = 0 := by
    rw [ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_right]
    rw [← ContinuousLinearMap.star_eq_adjoint]
    change (@inner ℂ E _ y ((star (U - 1) * (U - 1)) y)).re = 0
    rw [← cfcHom_distanceToOneSqComplex U hU, ← hrepr, hintegral]
  have hUy : U y = y := by
    have hzeroNorm : ‖(U - 1) y‖ = 0 := sq_eq_zero_iff.mp hnormSq
    have hzero : (U - 1) y = 0 := norm_eq_zero.mp hzeroNorm
    simpa only [sub_apply, one_apply_eq_self, sub_eq_zero] using hzero
  rw [zero_apply]
  change y = (0 : E)
  exact hNoFixed y hUy
