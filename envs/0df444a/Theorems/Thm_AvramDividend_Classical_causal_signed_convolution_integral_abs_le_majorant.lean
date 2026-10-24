-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_signed_convolution_integral_abs_le_majorant
-- name    : AvramDividend.Classical.causal_signed_convolution_integral_abs_le_majorant
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T12:07:08.348496+00:00
-- url     : https://prove2.me/theorems/a3bbc227-0c8b-49ec-bb0a-62b397ef9662
-- title:
--   Absolute signed causal convolution integral bounded by a positive envelope
-- statement:
--   For two causal products on (0,x] with interval-integrable integrands, if each factor of the signed product is dominated by its corresponding nonnegative majorant, then the absolute signed causal convolution integral is bounded by the positive-envelope convolution integral. This is the key bridge from signed Volterra resolvent terms to positive kernel-power bounds.
-- source:
--   Gaussian scale-function C2 Neumann-resolvent series, domination step, using pinned Mathlib interval integral triangle and monotonicity inequalities.

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open MeasureTheory Set

theorem AvramDividend.Classical.causal_signed_convolution_integral_abs_le_majorant
    (k κ f F : ℝ → ℝ) (x : ℝ) (hx : 0 < x)
    (hint : IntervalIntegrable (fun s : ℝ => k (x - s) * f s) volume 0 x)
    (hmajor : IntervalIntegrable (fun s : ℝ => κ (x - s) * F s) volume 0 x)
    (hk : ∀ s ∈ Ioo (0 : ℝ) x, |k (x - s)| ≤ κ (x - s))
    (hf : ∀ s ∈ Ioo (0 : ℝ) x, |f s| ≤ F s)
    (hκ : ∀ s ∈ Ioo (0 : ℝ) x, 0 ≤ κ (x - s)) :
    |∫ s in (0 : ℝ)..x, k (x - s) * f s| ≤
      ∫ s in (0 : ℝ)..x, κ (x - s) * F s := by sorry
