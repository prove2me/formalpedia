-- Prove2me | solution 1 for section5_ideal_phase_neg
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:00:54.522621+00:00
-- url     : https://prove2.me/submissions/8714bf38-fb38-40a5-89a5-8bf7e20deef9

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
import Definitions.Def_Section5Verified_Section5ProductSampling
import Mathlib
import Theorems.Thm_section5_gaussian_disagreement_proved
import Theorems.Thm_section5_gaussian_pi_density
import Theorems.Thm_section5_ideal_phase_distance_sq
import Theorems.Thm_section5_l2_norm_sq
namespace «Aux_w_53_hermite»
end «Aux_w_53_hermite»
section
set_option autoImplicit false

open MeasureTheory ProbabilityTheory Aux_w_53_hermite QuantumLTF.Example

/-! Gaussian density and tail estimates for Appendix D, Eq. 230. -/









theorem section5_gaussian_density_nonneg (n : ℕ) (x : Fin n → ℝ) :
    0 ≤ section5_gaussian_density n x := Finset.prod_nonneg (fun _ _ => (phi_pos _).le)









theorem section5_gaussian_density_integral_set (n : ℕ) (s : Set (Fin n → ℝ))
    (hs : MeasurableSet s) :
    (∫ x in s, section5_gaussian_density n x
      ∂(Measure.pi (fun _ : Fin n => (volume : Measure ℝ)))) =
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1)).real s := by
  rw [section5_gaussian_pi_density]
  change _ = (((Measure.pi (fun _ : Fin n => (volume : Measure ℝ))).withDensity
    (fun x => ENNReal.ofReal (section5_gaussian_density n x))) s).toReal
  rw [withDensity_apply _ hs,
    ← ofReal_integral_eq_lintegral_ofReal (section5_gaussian_density_integrable n).integrableOn
      (Filter.Eventually.of_forall (section5_gaussian_density_nonneg n)),
    ENNReal.toReal_ofReal (integral_nonneg (section5_gaussian_density_nonneg n))]









theorem section5_gaussian_amplitude_unit (n : ℕ) :
    (∫ x, ‖section5_gaussian_amplitude n x‖^2
      ∂(Measure.pi (fun _ : Fin n => (volume : Measure ℝ)))) = 1 := by
  simp_rw [section5_gaussian_amplitude_norm_sq]
  rw [← setIntegral_univ,section5_gaussian_density_integral_set n Set.univ MeasurableSet.univ]
  simp













end
section
set_option autoImplicit false

open MeasureTheory

/-! Product-space estimates for the multivariate Hermite sampling argument.
All product integrals are justified before Fubini is used.
-/











































theorem section5_unit_phase_l2_norm {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (u f : α → ℂ) (hu : AEStronglyMeasurable u μ) (hf : MemLp f 2 μ)
    (hunit : ∀ x, ‖u x‖=1) :
    ‖(section5_unit_phase_memLp u f hu hf hunit).toLp (fun x => u x*f x)‖ = ‖hf.toLp f‖ := by
  have hsq : ‖(section5_unit_phase_memLp u f hu hf hunit).toLp (fun x => u x*f x)‖^2 =
      ‖hf.toLp f‖^2 := by
    rw [section5_l2_norm_sq,section5_l2_norm_sq]
    simp only [norm_mul,hunit,one_mul]
  nlinarith [norm_nonneg ((section5_unit_phase_memLp u f hu hf hunit).toLp (fun x => u x*f x)),
    norm_nonneg (hf.toLp f)]





end
section
set_option autoImplicit false

open MeasureTheory QAlgorithms QuantumLTF.Example QuantumLTF.Membership

/-! Both signs of the orientation test, including zero inner products on the finite grid. -/

theorem section5_ideal_phase_norm {n : ℕ} (w : EuclideanSpace ℝ (Fin n)) :
    ‖(section5_ideal_phase_memLp w).toLp (section5_ideal_phase_state w)‖=1 := by
  have hunit := section5_unit_phase_l2_norm (section5_ltf_phase w) (section5_gaussian_amplitude n)
    (section5_ltf_phase_measurable w).aestronglyMeasurable
    (section5_gaussian_amplitude_memLp n) (section5_ltf_phase_norm w)
  change ‖(section5_ideal_phase_memLp w).toLp (section5_ideal_phase_state w)‖ =
    ‖(section5_gaussian_amplitude_memLp n).toLp (section5_gaussian_amplitude n)‖ at hunit
  have hsq : ‖(section5_gaussian_amplitude_memLp n).toLp (section5_gaussian_amplitude n)‖^2=1 := by
    rw [section5_l2_norm_sq]
    exact section5_gaussian_amplitude_unit n
  nlinarith [norm_nonneg ((section5_gaussian_amplitude_memLp n).toLp (section5_gaussian_amplitude n))]









end
set_option autoImplicit false
open MeasureTheory QAlgorithms QuantumLTF.Example QuantumLTF.Membership
theorem solution {n : ℕ} (w : EuclideanSpace ℝ (Fin n)) (hw : ‖w‖=1) :
    (section5_ideal_phase_memLp (-w)).toLp (section5_ideal_phase_state (-w)) =
      -(section5_ideal_phase_memLp w).toLp (section5_ideal_phase_state w) := by
  have hnw : ‖-w‖=1 := by simpa only [norm_neg] using hw
  have hdis : disagree (ltf w 0) (ltf (-w) 0)=1 := by
    have hh := (section5_gaussian_disagreement_proved w (-w) hw hnw 0 0).2
    simpa only [inner_neg_right,real_inner_self_eq_norm_sq,hw,one_pow,
      Real.arccos_neg_one,div_self Real.pi_ne_zero] using hh
  let A := (section5_ideal_phase_memLp w).toLp (section5_ideal_phase_state w)
  let B := (section5_ideal_phase_memLp (-w)).toLp (section5_ideal_phase_state (-w))
  have he := section5_ideal_phase_distance_sq w (-w)
  rw [hdis] at he
  have hp := parallelogram_law_with_norm ℂ A B
  have hA : ‖A‖=1 := section5_ideal_phase_norm w
  have hB : ‖B‖=1 := section5_ideal_phase_norm (-w)
  rw [hA,hB] at hp
  have hz : A+B=0 := norm_eq_zero.mp (by nlinarith [norm_nonneg (A+B)])
  change B = -A
  apply eq_neg_iff_add_eq_zero.mpr
  simpa only [add_comm] using hz
