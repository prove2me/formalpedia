-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_negative_jumps_levy_integrable
-- name    : AvramDividend.Classical.esscher_negative_jumps_levy_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T22:18:26.828589+00:00
-- url     : https://prove2.me/theorems/ee738536-def1-42f4-8679-4954f9c0d1a3
-- title:
--   Esscher nonnegative exponential tilt preserves Lévy jump integrability
-- statement:
--   For a spectrally negative Lévy jump measure ν supported on (-∞,0), a nonnegative Esscher exponent φ produces the tilted measure exp(φ y)ν(dy). Since exp(φy)≤1 on all negative jumps, the Lévy integrability condition ∫min(1,y²)ν(dy)<∞ transfers without any extra moment hypothesis. This is a deterministic measure-theoretic prerequisite for constructing the shifted Lévy triplet used in the Gaussian, infinite-small-jump and bounded-variation excursion cases.
-- source:
--   Pinned Mathlib lintegral_withDensity_eq_lintegral_mul, lintegral_mono_ae, Real.exp_le_one_iff, ENNReal.ofReal_le_one; canonical Avram SpectrallyNegativeLevy.ν_integrable.

import Mathlib
open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.esscher_negative_jumps_levy_integrable
    (ν : Measure ℝ) (φ : ℝ) (hφ : 0 ≤ φ)
    (hneg : ν (Ici 0) = 0)
    (hlevy : (∫⁻ y : ℝ, ENNReal.ofReal (min 1 (y ^ 2)) ∂ν) < ⊤) :
    (∫⁻ y : ℝ, ENNReal.ofReal (min 1 (y ^ 2))
      ∂(ν.withDensity (fun y : ℝ => ENNReal.ofReal (Real.exp (φ * y))))) < ⊤ := by sorry
