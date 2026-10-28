-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_shifted_renewal_density_interval_integrable_at_zero
-- name    : AvramDividend.Classical.causal_shifted_renewal_density_interval_integrable_at_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T10:30:23.209798+00:00
-- url     : https://prove2.me/theorems/badcb7d5-296b-4bbb-aa81-f2bfe5d2da70
-- title:
--   Zero-endpoint interval integrability of scaled shifted renewal density
-- statement:
--   A pointwise summable positive-time renewal-power series that is interval-integrable from zero retains that property after the conventional zero-index shift and multiplication by an arbitrary real scale coefficient. This transfers the new zero-endpoint integrability theorem into the exact b-times-shifted-series expression appearing in the open BV Esscher scale representation.

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Theorems.Thm_AvramDividend_Classical_causal_renewal_shifted_tsum_eq_unshifted

open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.causal_shifted_renewal_density_interval_integrable_at_zero
    (F : ℕ → ℝ → ℝ) (b : ℝ)
    (hpoint : ∀ y : ℝ, 0 < y → Summable (fun n : ℕ => F n y))
    (hint : ∀ x : ℝ, 0 < x →
      IntervalIntegrable (fun y : ℝ => ∑' n : ℕ, F n y) volume 0 x) :
    ∀ x : ℝ, 0 < x →
      IntervalIntegrable
        (fun y : ℝ => b * ∑' n : ℕ,
          if n = 0 then (0 : ℝ) else F (n - 1) y)
        volume 0 x := by sorry
