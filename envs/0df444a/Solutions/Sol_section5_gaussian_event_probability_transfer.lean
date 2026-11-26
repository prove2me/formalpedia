-- Prove2me | solution 1 for section5_gaussian_event_probability_transfer
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:28:09.079817+00:00
-- url     : https://prove2.me/submissions/e9dc6267-d346-45f1-a1ba-77def333fcfe

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Membership_Supplement_band1D53
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight
import Definitions.Def_QuantumLTF_Membership_Supplement_hermCoeff
import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5GaussianProbabilityTransfer
import Definitions.Def_Section5Verified_Section5GaussianSampling
import Definitions.Def_Section5Verified_Section5GaussianTail
import Definitions.Def_Section5Verified_Section5HermiteFoundations
import Mathlib
import Theorems.Thm_section5_continuous_event_stability
import Theorems.Thm_section5_gaussian_pi_density
import Theorems.Thm_section5_gaussian_sampling_full
import Theorems.Thm_section5_l2_norm_sq
import Theorems.Thm_section5_sampled_gaussian_toLp_ne_zero
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







































theorem section5_l2_distance {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f g : α → ℂ) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Real.sqrt (∫ x, ‖f x-g x‖^2 ∂μ) = ‖hf.toLp f-hg.toLp g‖ := by
  change Real.sqrt (∫ x, ‖(f-g) x‖^2 ∂μ) = _
  rw [← section5_l2_norm_sq (f-g) (hf.sub hg),MemLp.toLp_sub,
    Real.sqrt_sq (norm_nonneg _)]





theorem section5_normalization_displacement {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (x : V) (hx : x ≠ 0) :
    ‖NormedSpace.normalize x-x‖ = |1-‖x‖| := by
  have heq : NormedSpace.normalize x-x = (1-‖x‖) • NormedSpace.normalize x := by
    rw [sub_smul,one_smul,NormedSpace.norm_smul_normalize]
  rw [heq,norm_smul,NormedSpace.norm_normalize hx,mul_one,Real.norm_eq_abs]

/-- Normalization costs only the amplitude error, so the label-boundary error
appears once rather than twice in Appendix D, Eq. 235. -/
theorem section5_phase_normalization_bound {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (A B R P : V) (hR : R ≠ 0) (hnorm : ‖R‖=‖A‖)
    (hB : ‖B‖=1) (G E : ℝ) (hamp : ‖A-B‖ ≤ G) (hphase : ‖R-P‖ ≤ G+E) :
    ‖NormedSpace.normalize R-P‖ ≤ 2*G+E := by
  have hnormerr : |1-‖R‖| ≤ G := by
    rw [hnorm,abs_sub_comm,← hB]
    exact (abs_norm_sub_norm_le A B).trans hamp
  calc
    _ ≤ ‖NormedSpace.normalize R-R‖+‖R-P‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ = |1-‖R‖|+‖R-P‖ := by rw [section5_normalization_displacement R hR]
    _ ≤ G+(G+E) := add_le_add hnormerr hphase
    _ = _ := by ring

end
section
set_option autoImplicit false

open MeasureTheory

/-! Normalized discretized Gaussian probabilities compared to the continuous Gaussian. -/



theorem section5_normalized_gaussian_error (n M : ℕ) (hM : 0 < M)
    (hsize : 128*(n:ℝ)^2 ≤ M) :
    ‖section5_normalized_sampled_gaussian n M hM-
      (section5_gaussian_amplitude_memLp n).toLp (section5_gaussian_amplitude n)‖ ≤
      4*n*Real.sqrt (32/M)+2*Real.sqrt (2*n)*Real.exp (-Real.pi*M/4) := by
  let A := (section5_sampled_gaussian_memLp n M hM).toLp (section5_sampled_gaussian_amplitude n M)
  let B := (section5_gaussian_amplitude_memLp n).toLp (section5_gaussian_amplitude n)
  let G := 2*n*Real.sqrt (32/M)+Real.sqrt (2*n)*Real.exp (-Real.pi*M/4)
  have hBn : ‖B‖=1 := by
    have hsq : ‖B‖^2=1 := by
      rw [section5_l2_norm_sq]
      exact section5_gaussian_amplitude_unit n
    nlinarith [norm_nonneg B]
  have herror : ‖A-B‖ ≤ G := by
    rw [← section5_l2_distance _ _ (section5_sampled_gaussian_memLp n M hM)
      (section5_gaussian_amplitude_memLp n)]
    exact section5_gaussian_sampling_full n M hM hsize
  have hh := section5_phase_normalization_bound A B A B
    (section5_sampled_gaussian_toLp_ne_zero n M hM) rfl hBn G 0 herror
    (by simpa only [add_zero] using herror)
  change ‖NormedSpace.normalize A-B‖ ≤ _
  dsimp only [G] at hh
  linarith



end
set_option autoImplicit false
open MeasureTheory
theorem solution (n M : ℕ) (hM : 0 < M)
    (hsize : 128*(n:ℝ)^2 ≤ M) (s : Set (Fin n → ℝ)) (hs : MeasurableSet s) :
    |(∫ x in s, ‖section5_normalized_sampled_gaussian n M hM x‖^2
      ∂(Measure.pi (fun _ : Fin n => (volume : Measure ℝ))))-
        (Measure.pi (fun _ : Fin n => ProbabilityTheory.gaussianReal 0 1)).real s| ≤
      8*n*Real.sqrt (32/M)+4*Real.sqrt (2*n)*Real.exp (-Real.pi*M/4) := by
  let A := section5_normalized_sampled_gaussian n M hM
  let B := section5_gaussian_amplitude n
  have hnA : ‖A‖=1 := NormedSpace.norm_normalize (section5_sampled_gaussian_toLp_ne_zero n M hM)
  have hnB : ‖(section5_gaussian_amplitude_memLp n).toLp B‖=1 := by
    have hsq : ‖(section5_gaussian_amplitude_memLp n).toLp B‖^2=1 := by
      rw [section5_l2_norm_sq]
      exact section5_gaussian_amplitude_unit n
    nlinarith [norm_nonneg ((section5_gaussian_amplitude_memLp n).toLp B)]
  have hnA' : ‖(Lp.memLp A).toLp A‖ ≤ 1 := by rw [Lp.toLp_coeFn,hnA]
  have hh := section5_continuous_event_stability s hs A B (Lp.memLp A)
    (section5_gaussian_amplitude_memLp n) hnA' hnB.le
  rw [Lp.toLp_coeFn] at hh
  have heq : (∫ x in s, ‖B x‖^2
      ∂(Measure.pi (fun _ : Fin n => (volume : Measure ℝ)))) =
      (Measure.pi (fun _ : Fin n => ProbabilityTheory.gaussianReal 0 1)).real s := by
    simp only [B,section5_gaussian_amplitude_norm_sq]
    exact section5_gaussian_density_integral_set n s hs
  rw [heq] at hh
  have he := section5_normalized_gaussian_error n M hM hsize
  exact hh.trans (by nlinarith)
