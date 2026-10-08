-- Prove2me | Theorems.Thm_ConnesGreen_critical_mellin_density_integrable
-- name    : ConnesGreen.critical_mellin_density_integrable
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-08T03:00:50.250287+00:00
-- url     : https://prove2.me/theorems/5db80a54-4ffc-4b3e-abef-cb89a3dc67b2
-- title:
--   Original critical Mellin squared-transform density is integrable
-- statement:
--   For every unchanged smooth compactly supported original test g, the real function r -> |mellinHat(g,1/2+i r)|^2 is integrable over the full real line. The proof uses the original test as a Schwartz function, the Mathlib Fourier transform, and the exact frequency dictionary with rescaling -r/(2 pi). It establishes genuine full-line integrability without relying on total-integral defaults or an assumed convergence premise.
-- source:
--   monocap-tech/weil at 81bd36c79198ad2c58167b3ef2421d1c1e4439e2; ArchimedeanEnergy.lean. Original native declarations unchanged. Exact native definition normalization checks accompany both ports.

import Definitions.Def_ConnesRZ_weil_defs
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
set_option autoImplicit false
set_option maxHeartbeats 3000000
open Complex MeasureTheory ConnesRZ
open scoped FourierTransform
noncomputable section

theorem ConnesGreen.critical_mellin_density_integrable (g : ℝ → ℂ) (hg : IsTest g) :
    Integrable (fun r : ℝ => ‖mellinHat g (1/2 + I*r)‖ ^ 2) := by sorry
