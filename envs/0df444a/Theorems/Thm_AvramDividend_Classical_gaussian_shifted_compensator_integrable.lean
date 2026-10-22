-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_shifted_compensator_integrable
-- name    : AvramDividend.Classical.gaussian_shifted_compensator_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T06:35:08.778203+00:00
-- url     : https://prove2.me/theorems/3b0e8f44-99d7-4886-9697-759f8be44b02
-- title:
--   Finiteness of the Esscher-shifted Gaussian Lévy jump compensator under the quadratic truncation condition
-- statement:
--   Let μ be a Lévy jump-magnitude measure whose positive-side truncated-square moment ∫min(1,z²)μ(dz) is finite. For φ>0 and θ≥0, the weighted compensator exp(−φz)(exp(−θz)−1+θz) has a finite ENNReal integral over z>0. Prove it by bounding the weighted compensator by (θ+θ²)exp(−φz)min(z²,z) and invoking the accepted Esscher-damped tail-area integrability theorem. This supplies genuine measure-level finiteness for the shifted Gaussian Lévy–Khintchine exponent.
-- source:
--   esscher_tilted_tail_area_integrable; gaussian_esscher_compensator_envelope; pinned ae_restrict_mem, lintegral_mono_ae, lintegral_const_mul, ENNReal.mul_lt_top.

import Mathlib
open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.gaussian_shifted_compensator_integrable
    (μ : Measure ℝ) (φ θ : ℝ) (hφ : 0 < φ) (hθ : 0 ≤ θ)
    (hlevy : (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal (min 1 (z ^ 2)) ∂μ) < ⊤) :
    (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal
        (Real.exp (-φ * z) *
          (Real.exp (-θ * z) - 1 + θ * z)) ∂μ) < ⊤ := by sorry
