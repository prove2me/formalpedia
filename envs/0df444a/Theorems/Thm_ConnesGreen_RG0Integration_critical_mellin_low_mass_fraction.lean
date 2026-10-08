-- Prove2me | Theorems.Thm_ConnesGreen_RG0Integration_critical_mellin_low_mass_fraction
-- name    : ConnesGreen.RG0Integration.critical_mellin_low_mass_fraction
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-07T22:46:42.516164+00:00
-- url     : https://prove2.me/theorems/69b9e1de-6733-4f06-865d-7112d75e567e
-- title:
--   Original low-frequency Mellin mass fraction from support length and exact Fourier normalization
-- statement:
--   For $B,T\ge0$ and an original smooth test supported in $(-T,T)$, $$\int_{-B}^{B}|\widehat g(\tfrac12+ir)|^2\,dr\le\frac{2BT}{\pi}\int_{\mathbb R}|\widehat g(\tfrac12+ir)|^2\,dr.$$ Genuine Fourier-density integrability follows from the Schwartz transform. The load-bearing accepted support-mass bound and exact $2\pi$ mass identity yield the displayed relative concentration estimate. This joins milestones 28 and 31, with milestone 30 reused by the revised accepted proof of 31; no gamma-symbol or full Weil positivity estimate is assumed.
-- source:
--   monocap-tech/weil, original native companion and RG0DependencyIntegration.lean. Source/proof cuts and declarations are extracted with the Lean elaborator. Original carrier, actual zeros, multiplicities and reflected /2 custody retained.

import Theorems.Thm_ConnesGreen_supported_mellin_norm_sq_mass_bound
import Theorems.Thm_ConnesGreen_critical_mellin_mass_identity
import Definitions.Def_ConnesGreen_canonical_model
set_option autoImplicit false
set_option maxHeartbeats 3000000
open Complex MeasureTheory ConnesRZ ConnesGreen WeilDefect.ConnesNative Set
open scoped FourierTransform
noncomputable section
private theorem mellin_fourier_dictionary (g : ℝ → ℂ) (r : ℝ) :
    mellinHat g (1 / 2 + I * r) = 𝓕 g (-r / (2 * Real.pi)) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  unfold mellinHat
  simp only [add_sub_cancel_left]
  congr 1
  ext u
  rw [smul_eq_mul, mul_comm (g u)]
  congr 1
  have h : (-2 * Real.pi * u * (-r / (2 * Real.pi))) = r * u := by field_simp
  rw [h]
  push_cast
  ring

private theorem density_integrable (g : ℝ → ℂ) (hg : IsTest g) :
    Integrable (fun r : ℝ => ‖mellinHat g (1/2 + I*r)‖ ^ 2) := by
  let f := hg.2.toSchwartzMap (hg.1.of_le (by simp))
  have hd := (𝓕 f : SchwartzMap ℝ ℂ).memLp 2
  have hi := hd.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  rw [SchwartzMap.fourier_coe] at hi
  have hc := hi.comp_mul_left' (R := (-(1/(2*Real.pi)) : ℝ)) (by exact neg_ne_zero.mpr (div_ne_zero (by norm_num) (mul_ne_zero (by norm_num) Real.pi_ne_zero)))
  convert hc using 1
  ext r
  change ‖mellinHat g (1/2 + I*r)‖ ^ 2 = ‖𝓕 g (-(1/(2*Real.pi))*r)‖ ^ 2
  rw [mellin_fourier_dictionary]
  congr 2
  ring

theorem ConnesGreen.RG0Integration.critical_mellin_low_mass_fraction (B T : ℝ)
    (hB : 0 ≤ B) (hT : 0 ≤ T) (g : ℝ → ℂ) (hg : SupportedTest T g) :
    (∫ r in Icc (-B) B, ‖mellinHat g (1/2 + I*r)‖ ^ 2) ≤
      (2 * B * T / Real.pi) * (∫ r : ℝ, ‖mellinHat g (1/2 + I*r)‖ ^ 2) := by sorry
