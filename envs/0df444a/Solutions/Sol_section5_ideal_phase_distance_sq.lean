-- Prove2me | solution 1 for section5_ideal_phase_distance_sq
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:57:19.086029+00:00
-- url     : https://prove2.me/submissions/d554b6fb-7ab2-4654-ae7f-3e3f300d809f

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Example_qex
import Definitions.Def_QuantumLTF_Membership_Supplement_band1D53
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight
import Definitions.Def_QuantumLTF_Membership_Supplement_hermCoeff
import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_QuantumLTF_Membership_disagree
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_ltf
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5GaussianTail
import Definitions.Def_Section5Verified_Section5HermiteFoundations
import Definitions.Def_Section5Verified_Section5PhaseStateError
import Mathlib
import Theorems.Thm_section5_gaussian_pi_density
import Theorems.Thm_section5_l2_norm_sq
namespace «Aux_w_53_hermite»
end «Aux_w_53_hermite»
section
set_option autoImplicit false

open MeasureTheory ProbabilityTheory Aux_w_53_hermite QuantumLTF.Example

/-! Gaussian density and tail estimates for Appendix D, Eq. 230. -/









theorem section5_gaussian_density_nonneg (n : ℕ) (x : Fin n → ℝ) :
    0 ≤ section5_gaussian_density n x := Finset.prod_nonneg (fun _ _ => (phi_pos _).le)

theorem section5_gaussian_density_continuous (n : ℕ) : Continuous (section5_gaussian_density n) :=
  continuous_finsetProd _ (fun i _ => continuous_phi.comp (continuous_apply i))









theorem section5_gaussian_change_density (n : ℕ) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (F : (Fin n → ℝ) → E) :
    (∫ x, F x ∂(Measure.pi (fun _ : Fin n => gaussianReal 0 1))) =
      ∫ x, section5_gaussian_density n x • F x
        ∂(Measure.pi (fun _ : Fin n => (volume : Measure ℝ))) := by
  rw [section5_gaussian_pi_density,
    integral_withDensity_eq_integral_toReal_smul
      (section5_gaussian_density_continuous n).measurable.ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (section5_gaussian_density_nonneg n _)]





















end
section
set_option autoImplicit false

open MeasureTheory ProbabilityTheory QuantumLTF.Membership QuantumLTF.Example

/-! Gaussian orientation errors after coordinate rounding, using the mission's already-Proved
Gaussian disagreement lemma (Lemma 2.1), with its accepted proof checked locally. -/

theorem section5_ltf_measurable {n : ℕ} (w : EuclideanSpace ℝ (Fin n)) (θ : ℝ) :
    Measurable (ltf w θ) := by
  unfold ltf sgn
  exact Measurable.ite (measurableSet_le measurable_const (by fun_prop))
    measurable_const measurable_const









end
section
set_option autoImplicit false

open MeasureTheory ProbabilityTheory QAlgorithms QuantumLTF.Example QuantumLTF.Membership

/-! Orientation testing as an exact squared distance of phase states. -/

theorem section5_ltf_difference_integral {n : ℕ} (w u : EuclideanSpace ℝ (Fin n)) :
    (∫ x, (((ltf w 0 x-ltf u 0 x : ℤ):ℝ)^2)
      ∂(stdGaussian (EuclideanSpace ℝ (Fin n)))) = 4*disagree (ltf w 0) (ltf u 0) := by
  let S := {x | ltf w 0 x ≠ ltf u 0 x}
  have hs : MeasurableSet S :=
    (measurableSet_eq_fun (section5_ltf_measurable w 0) (section5_ltf_measurable u 0)).compl
  have heq : (fun x => (((ltf w 0 x-ltf u 0 x : ℤ):ℝ)^2))=S.indicator (fun _ => (4:ℝ)) := by
    funext x
    simp only [S,Set.indicator_apply,Set.mem_ofPred_eq]
    unfold ltf sgn
    split_ifs <;> norm_num at *
  rw [heq,integral_indicator hs,setIntegral_const]
  change (stdGaussian (EuclideanSpace ℝ (Fin n))).real S * 4 = _
  rw [mul_comm]
  rfl







end
set_option autoImplicit false
open MeasureTheory ProbabilityTheory QAlgorithms QuantumLTF.Example QuantumLTF.Membership
theorem solution {n : ℕ} (w u : EuclideanSpace ℝ (Fin n)) :
    ‖(section5_ideal_phase_memLp w).toLp (section5_ideal_phase_state w)-
      (section5_ideal_phase_memLp u).toLp (section5_ideal_phase_state u)‖^2 =
        4*disagree (ltf w 0) (ltf u 0) := by
  have hmeas : Measurable (fun x : EuclideanSpace ℝ (Fin n) =>
      (((ltf w 0 x-ltf u 0 x : ℤ):ℝ)^2)) :=
    ((measurable_of_countable (fun z : ℤ => (z:ℝ))).comp
      ((section5_ltf_measurable w 0).sub (section5_ltf_measurable u 0))).pow_const 2
  have hi := section5_ltf_difference_integral w u
  rw [← ProbabilityTheory.map_pi_eq_stdGaussian,
    integral_map (PiLp.lipschitzWith_toLp 2 (fun _ : Fin n => ℝ)).continuous.measurable.aemeasurable
      hmeas.aestronglyMeasurable,section5_gaussian_change_density n] at hi
  have hLp : (section5_ideal_phase_memLp w).toLp (section5_ideal_phase_state w)-
      (section5_ideal_phase_memLp u).toLp (section5_ideal_phase_state u) =
      ((section5_ideal_phase_memLp w).sub (section5_ideal_phase_memLp u)).toLp
        (section5_ideal_phase_state w-section5_ideal_phase_state u) := rfl
  rw [hLp,section5_l2_norm_sq]
  rw [← hi]
  apply integral_congr_ae
  filter_upwards with x
  have heq : section5_ideal_phase_state w x-section5_ideal_phase_state u x =
      ((((ltf w 0 (WithLp.toLp 2 x)-ltf u 0 (WithLp.toLp 2 x) : ℤ):ℝ):ℂ))*
        section5_gaussian_amplitude n x := by
    unfold section5_ideal_phase_state section5_ltf_phase
    push_cast
    ring
  change ‖section5_ideal_phase_state w x-section5_ideal_phase_state u x‖^2 = _
  rw [heq,norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs,
    section5_gaussian_amplitude_norm_sq]
  change _ = section5_gaussian_density n x * _
  ring
