-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_Ioc_convolution_powers_nonnegative
-- name    : AvramDividend.Classical.causal_Ioc_convolution_powers_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T12:46:55.930992+00:00
-- url     : https://prove2.me/theorems/e304fe7d-ac62-4130-a77b-478e9c9bc3ed
-- title:
--   Positive causal convolution powers remain nonnegative with Ioc-integral recursion
-- statement:
--   For an L1-style causal recursion using the positive-half-line interval (0,x] as a set integral, nonnegative kernel values imply nonnegative convolution powers for every nonnegative time. Conversion to the oriented real interval integral validates the positivity induction and reconciles the recursion used by the L1 mass theorem with the interval-only positivity theorem.
-- source:
--   Induction, intervalIntegral.integral_of_le, and intervalIntegral.integral_nonneg with nonnegative factors.

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open MeasureTheory Set

theorem AvramDividend.Classical.causal_Ioc_convolution_powers_nonnegative
    (κ : ℝ → ℝ) (F : ℕ → ℝ → ℝ)
    (hzero : F 0 = κ)
    (hsucc : ∀ n : ℕ, F (n + 1) =
      fun x : ℝ => ∫ s in Ioc (0 : ℝ) x,
        κ s * F n (x - s) ∂volume)
    (hκ : ∀ t : ℝ, 0 ≤ t → 0 ≤ κ t) :
    ∀ n : ℕ, ∀ x : ℝ, 0 ≤ x → 0 ≤ F n x := by sorry
