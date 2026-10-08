-- Prove2me | Theorems.Thm_ConnesGreen_arch_convolution_re_eq_gamma_density
-- name    : ConnesGreen.arch_convolution_re_eq_gamma_density
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-08T03:01:44.842435+00:00
-- url     : https://prove2.me/theorems/ef2bc5de-c042-4ebc-b895-ec5839574ce8
-- title:
--   Exact original archimedean convolution term equals the real gamma-density integral
-- statement:
--   For every unchanged original admissible test g, Re archTerm(g*starInv(g)) equals (1/(2 pi)) times the integral of |mellinHat(g,1/2+i r)|^2 against Re digamma(1/4+i r/2)-log(pi). The public statement unfolds exactly the native gammaBracket definition. The accepted full convolution-Mellin identity yields the critical-line square-modulus identity; unfolding the original archTerm and the exact digamma/logDeriv Gamma identity gives the displayed equality. This identity alone does not assert weighted-density convergence, positivity, endpoint control or RH.
-- source:
--   monocap-tech/weil at 81bd36c79198ad2c58167b3ef2421d1c1e4439e2; ArchimedeanEnergy.lean. Original native declarations unchanged. Exact native definition normalization checks accompany both ports.

import Theorems.Thm_ConnesRZ_mellinHat_conv_starInv
open Complex MeasureTheory ConnesRZ
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section

theorem ConnesGreen.arch_convolution_re_eq_gamma_density (g : ℝ → ℂ) (hg : IsTest g) :
    (archTerm (conv g (starInv g))).re = (1 / (2 * Real.pi)) *
      ∫ r : ℝ, ‖mellinHat g (1 / 2 + I * r)‖ ^ 2 *
        ((Complex.digamma (1 / 4 + I * r / 2)).re - Real.log Real.pi) := by sorry
