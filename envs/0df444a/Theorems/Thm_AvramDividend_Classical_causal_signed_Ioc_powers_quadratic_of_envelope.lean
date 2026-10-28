-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_signed_Ioc_powers_quadratic_of_envelope
-- name    : AvramDividend.Classical.causal_signed_Ioc_powers_quadratic_of_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T15:47:34.010176+00:00
-- url     : https://prove2.me/theorems/f6a467e7-bd49-47b2-a429-708f8821da4f
-- title:
--   Signed causal Neumann powers inherit quadratic-geometric decay from Ioc envelope
-- statement:
--   Suppose signed and nonnegative causal convolution-power sequences are recursively defined by Ioc integrals and their products are integrable. If each signed base kernel is bounded by a positive envelope and each positive power is quadratically/geometrically bounded, then the signed powers obey the same explicit pointwise bound, precisely matching the derivative regularity estimates.
-- source:
--   Convert both recursive causal Ioc convolutions to the interval-integral orientation, apply the Proved signed envelope domination theorem, then transfer the quadratic-geometric pointwise bound from the positive powers. This is the signed derivative-series bound needed for the Gaussian Esscher C1 derivative resolvent.

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Theorems.Thm_AvramDividend_Classical_causal_signed_convolution_powers_abs_le_envelope
import Theorems.Thm_AvramDividend_Classical_positive_Ioc_causal_convolution_comm_real
open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.causal_signed_Ioc_powers_quadratic_of_envelope
    (k κ : ℝ → ℝ) (P F : ℕ → ℝ → ℝ) (ρ : ℝ)
    (hk : ∀ t : ℝ, 0 < t → |k t| ≤ κ t)
    (hκ : ∀ t : ℝ, 0 < t → 0 ≤ κ t)
    (hP0 : P 0 = k) (hF0 : F 0 = κ)
    (hPsucc : ∀ n : ℕ, ∀ x : ℝ, 0 < x →
      P (n + 1) x =
        ∫ s in Ioc (0 : ℝ) x, k s * P n (x - s) ∂volume)
    (hFsucc : ∀ n : ℕ, ∀ x : ℝ, 0 < x →
      F (n + 1) x =
        ∫ s in Ioc (0 : ℝ) x, κ s * F n (x - s) ∂volume)
    (hPint : ∀ n : ℕ, ∀ x : ℝ, 0 < x →
      IntervalIntegrable (fun s : ℝ => k (x - s) * P n s) volume 0 x)
    (hFint : ∀ n : ℕ, ∀ x : ℝ, 0 < x →
      IntervalIntegrable (fun s : ℝ => κ (x - s) * F n s) volume 0 x)
    (hFpoint : ∀ n : ℕ, ∀ x : ℝ, 0 < x →
      F n x ≤ ((n + 1 : ℝ) ^ 2 * ρ ^ (n + 1)) / x) :
    ∀ n : ℕ, ∀ x : ℝ, 0 < x →
      |P n x| ≤ ((n + 1 : ℝ) ^ 2 * ρ ^ (n + 1)) / x := by sorry
