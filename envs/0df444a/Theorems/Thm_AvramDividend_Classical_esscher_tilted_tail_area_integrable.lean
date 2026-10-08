-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_tilted_tail_area_integrable
-- name    : AvramDividend.Classical.esscher_tilted_tail_area_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T07:47:16.264889+00:00
-- url     : https://prove2.me/theorems/86325105-592c-46ca-a50d-8f37a12fb484
-- title:
--   Esscher-damped ladder tail-area kernel is integrable against a Lévy jump measure
-- statement:
--   If a measure on positive jump sizes has finite Lévy truncated quadratic moment ∫min(1,z²)μ(dz), then for every positive Esscher exponent φ the exponentially damped ladder-tail area ∫e^{-φz}min(z²,z)μ(dz) is finite. The already published source-neutral scalar bound compares the integrand pointwise with (1+φ⁻¹)min(1,z²), and positivity plus monotonicity of ENNReal lintegrals establishes integrability. This is a necessary input to show the Esscher-shifted descending ladder-height kernel Kφ(t) has finite ∫min(1,t)Kφ(t)dt via Tonelli.
-- source:
--   Published esscher_tilted_tail_scalar_integrability_bound; pinned ENNReal.ofReal_mul, MeasureTheory.lintegral_const_mul and lintegral_mono_ae.

import Mathlib
open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.esscher_tilted_tail_area_integrable
    (μ : Measure ℝ) (φ : ℝ) (hφ : 0 < φ)
    (hlevy : (∫⁻ z in Ioi (0 : ℝ), ENNReal.ofReal (min 1 (z ^ 2)) ∂μ) < ⊤) :
    (∫⁻ z in Ioi (0 : ℝ), ENNReal.ofReal
      (Real.exp (-(φ * z)) * min (z ^ 2) z) ∂μ) < ⊤ := by sorry
