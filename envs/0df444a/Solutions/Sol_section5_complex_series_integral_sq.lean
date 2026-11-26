-- Prove2me | solution 1 for section5_complex_series_integral_sq
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:09:50.763041+00:00
-- url     : https://prove2.me/submissions/7cb75618-e73f-47bb-adb4-c5ea8167e102

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Membership_Supplement_band1D53
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight
import Definitions.Def_QuantumLTF_Membership_Supplement_hermCoeff
import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5HermiteWavefunctions
import Mathlib
import Theorems.Thm_section5_wave_sum_integrable_product
import Theorems.Thm_section5_wave_sum_product_integral
section
set_option autoImplicit false

open MeasureTheory Aux_w_53_hermite

/-! The normalized Hermite functions and the derivative estimate required by Appendix D. -/



















theorem section5_wave_sum_norm_sq {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (u : ι → ℕ) (hu : Function.Injective u) :
    (∫ x : ℝ, (∑ i, a i*section5_hermite_wave (u i) x)^2) = ∑ i, (a i)^2 := by
  classical
  simp_rw [pow_two]
  rw [section5_wave_sum_product_integral]
  simp [hu.eq_iff]





















theorem section5_hermite_series_integrable_sq {D : ℕ} (c : Fin D → ℝ) :
    Integrable (fun x => (section5_hermite_series c x)^2) := by
  simpa only [section5_hermite_series, pow_two] using
    section5_wave_sum_integrable_product c c (fun k : Fin D => (k:ℕ)) (fun k => (k:ℕ))



theorem section5_hermite_series_integral_sq {D : ℕ} (c : Fin D → ℝ) :
    (∫ x : ℝ, (section5_hermite_series c x)^2) = ∑ k, (c k)^2 :=
  section5_wave_sum_norm_sq c (fun k : Fin D => (k:ℕ)) Fin.val_injective













theorem section5_complex_hermite_series_re {D : ℕ} (c : Fin D → ℂ) (x : ℝ) :
    (section5_complex_hermite_series c x).re = section5_hermite_series (fun k => (c k).re) x := by
  simp [section5_complex_hermite_series, section5_hermite_series, Complex.mul_re]

theorem section5_complex_hermite_series_im {D : ℕ} (c : Fin D → ℂ) (x : ℝ) :
    (section5_complex_hermite_series c x).im = section5_hermite_series (fun k => (c k).im) x := by
  simp [section5_complex_hermite_series, section5_hermite_series, Complex.mul_im]















end
set_option autoImplicit false
open MeasureTheory QuantumLTF.Example Aux_w_53_hermite
theorem solution {D : ℕ} (c : Fin D → ℂ) :
    (∫ x : ℝ, ‖section5_complex_hermite_series c x‖^2) = ∑ k, ‖c k‖^2 := by
  let cr := fun k => (c k).re
  let ci := fun k => (c k).im
  have heq (x : ℝ) : ‖section5_complex_hermite_series c x‖^2 =
      (section5_hermite_series cr x)^2+(section5_hermite_series ci x)^2 := by
    rw [Complex.sq_norm,Complex.normSq_apply]
    simp only [section5_complex_hermite_series_re,section5_complex_hermite_series_im,cr,ci,pow_two]
  simp_rw [heq]
  rw [integral_add (section5_hermite_series_integrable_sq cr)
    (section5_hermite_series_integrable_sq ci),section5_hermite_series_integral_sq,
    section5_hermite_series_integral_sq,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  change (c k).re^2+(c k).im^2 = ‖c k‖^2
  rw [Complex.sq_norm,Complex.normSq_apply]
  ring
