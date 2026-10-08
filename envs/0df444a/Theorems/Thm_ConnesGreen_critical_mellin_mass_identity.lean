-- Prove2me | Theorems.Thm_ConnesGreen_critical_mellin_mass_identity
-- name    : ConnesGreen.critical_mellin_mass_identity
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-07T20:02:22.392041+00:00
-- url     : https://prove2.me/theorems/44a5534e-fade-434c-8fc1-45fb40f2b821
-- title:
--   Exact original Mellin critical-line Fourier mass normalization
-- statement:
--   For every original smooth compactly supported Connes test $g:\mathbb R\to\mathbb C$, let $\widehat g(z)=\int_{\mathbb R}g(t)e^{(z-1/2)t}\,dt$. Then $$\int_{\mathbb R}|\widehat g(\tfrac12+ir)|^2\,dr=2\pi\int_{\mathbb R}|g(t)|^2\,dt.$$ The factor is exact for the original positive-exponent transform. Smooth compact support supplies Fourier integrability; there is no extra convergence or positivity premise. This mass normalization supports a lower bound for the original gamma/digamma archimedean term and does not establish Weil positivity or RH.
-- source:
--   monocap-tech/weil, Connes/ArchimedeanEnergy.lean. Native proof uses existing Fourier inversion on the original convolution test. The standalone export independently uses Mathlib Schwartz Plancherel and the exact original Mellin/Fourier dictionary. Native companion results prove a uniform semibound for the full original Weil form and its original completed physical carrier, retaining the full actual-zero actor background.

import Definitions.Def_ConnesRZ_weil_defs
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
set_option autoImplicit false
set_option maxHeartbeats 3000000
open Complex MeasureTheory ConnesRZ
open scoped FourierTransform
noncomputable section

theorem ConnesGreen.critical_mellin_mass_identity (g : ℝ → ℂ) (hg : IsTest g) :
    (∫ r : ℝ, ‖mellinHat g (1 / 2 + I * r)‖ ^ 2) =
      2 * Real.pi * (∫ s : ℝ, ‖g s‖ ^ 2) := by sorry
