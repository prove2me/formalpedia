-- Prove2me | solution 1 for section5_gaussian_amplitude_tail
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:58:44.746074+00:00
-- url     : https://prove2.me/submissions/e4855736-7832-4cfe-ab92-d6c2ba952606

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Membership_Supplement_band1D53
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight
import Definitions.Def_QuantumLTF_Membership_Supplement_hermCoeff
import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5GaussianTail
import Definitions.Def_Section5Verified_Section5HermiteFoundations
import Mathlib
import Theorems.Thm_section5_gaussian_grid_tail_230
import Theorems.Thm_section5_gaussian_pi_density
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























end
namespace «Aux_w_53_hermite»
end «Aux_w_53_hermite»
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Aux_w_53_hermite QuantumLTF.Example
theorem solution (n M : ℕ) (hM : 0 < M) :
    Real.sqrt (∫ x in (section5_grid_box n M)ᶜ, ‖section5_gaussian_amplitude n x‖^2
      ∂(Measure.pi (fun _ : Fin n => (volume : Measure ℝ)))) ≤
        Real.sqrt (2*n)*Real.exp (-Real.pi*M/4) := by
  have hsub : (section5_grid_box n M)ᶜ ⊆
      {x : Fin n → ℝ | ∃ i, gridRadius M ≤ |x i|} := by
    intro x hx
    by_contra h
    change ¬ ∃ i : Fin n, gridRadius M ≤ |x i| at h
    push Not at h
    apply hx
    intro i hi
    exact ⟨(abs_lt.mp (h i)).1,(abs_lt.mp (h i)).2.le⟩
  simp_rw [section5_gaussian_amplitude_norm_sq]
  rw [section5_gaussian_density_integral_set n _ (section5_grid_box_measurable n M).compl]
  have hbound := (measureReal_mono (μ := Measure.pi (fun _ : Fin n => gaussianReal 0 1)) hsub).trans
    (section5_gaussian_grid_tail_230 n M hM)
  have hr := Real.sqrt_le_sqrt hbound
  have hexp : Real.exp (-Real.pi*M/2) = Real.exp (-Real.pi*M/4)^2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hexp,Real.sqrt_mul (by positivity),Real.sqrt_sq (Real.exp_pos _).le] at hr
  exact hr
