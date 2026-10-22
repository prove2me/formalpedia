-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_atom_lintegral
-- name    : AvramDividend.Classical.gaussian_double_tail_atom_lintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T06:47:01.420092+00:00
-- url     : https://prove2.me/theorems/27b8195a-7395-4c83-9f29-975256ed05a9
-- title:
--   ENNReal single-jump Gaussian double-tail integral bridge
-- statement:
--   For nonnegative θ,z, show the extended-nonnegative integral over (0,z] of θ²(z−t)exp(−θt) equals exp(−θz)−1+θz embedded in ENNReal. Convert the integral using nonnegativity, interval integrability, and the already-Proved real Gaussian double-tail atom identity. This is the per-atom integrability bridge needed to apply the already-Proved Tonelli identity to the full Lévy measure.
-- source:
--   Proved gaussian_double_tail_atom_integral; pinned ofReal_integral_eq_lintegral_ofReal, Continuous.integrableOn_Ioc and intervalIntegral.integral_of_le.

import Mathlib
open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.gaussian_double_tail_atom_lintegral
    (θ z : ℝ) (hθ : 0 ≤ θ) (hz : 0 ≤ z) :
    (∫⁻ t in Ioc (0 : ℝ) z,
      ENNReal.ofReal (θ ^ 2 * ((z - t) * Real.exp (-θ * t))) ∂volume) =
      ENNReal.ofReal (Real.exp (-θ * z) - 1 + θ * z) := by sorry
