-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_Ioc_convolution_powers_full_real_recursion
-- name    : AvramDividend.Classical.causal_Ioc_convolution_powers_full_real_recursion
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T19:22:57.255149+00:00
-- url     : https://prove2.me/theorems/d424ecf3-385f-4cf0-99fb-25a65442089c
-- title:
--   Causal positive-interval convolution powers vanish at nonpositive times and satisfy full real convolution
-- statement:
--   For any causal real kernel κ and a recursively defined positive-interval convolution power sequence F, prove inductively that all powers vanish on nonpositive times, and consequently identify the Ioc recurrence exactly with the full real Lebesgue convolution used by the corrected Esscher BV renewal kernel-series theorem. This uses the canonically Proved causal_real_convolution_equals_positive_interval_under_support and eliminates a representation mismatch between the existing positive-power mass theorem and the corrected bv_ac_esscher_scaled_renewal_kernel_series_data (9be5ada9).
-- source:
--   Accepted causal_real_convolution_equals_positive_interval_under_support and elementary emptiness of Ioc 0 x for x≤0.

import Theorems.Thm_AvramDividend_Classical_causal_real_convolution_equals_positive_interval_under_support

open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.causal_Ioc_convolution_powers_full_real_recursion
    (κ : ℝ → ℝ) (F : ℕ → ℝ → ℝ)
    (hκzero : ∀ x : ℝ, x ≤ 0 → κ x = 0)
    (hF0 : F 0 = κ)
    (hFsucc : ∀ n : ℕ, F (n + 1) =
      fun x : ℝ => ∫ y in Ioc (0 : ℝ) x,
        κ y * F n (x - y) ∂volume) :
    (∀ n : ℕ, ∀ x : ℝ, x ≤ 0 → F n x = 0) ∧
    (∀ n : ℕ, F (n + 1) =
      fun x : ℝ => ∫ y : ℝ, κ y * F n (x - y) ∂volume) := by sorry
