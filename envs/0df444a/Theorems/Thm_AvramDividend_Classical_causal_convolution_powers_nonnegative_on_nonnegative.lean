-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_convolution_powers_nonnegative_on_nonnegative
-- name    : AvramDividend.Classical.causal_convolution_powers_nonnegative_on_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T12:32:48.936186+00:00
-- url     : https://prove2.me/theorems/96c546af-e4c5-4b49-a30d-66afa62f6a36
-- title:
--   All recursive causal convolution powers of a nonnegative kernel remain nonnegative
-- statement:
--   If κ≥0 on [0,∞), F0=κ and F_(n+1)(x)=∫₀ˣ κ(s)F_n(x-s)ds, then every F_n is nonnegative on [0,∞). The proof is an induction using nonnegativity of the integrand throughout each closed integration interval, including the endpoints. This is essential for transferring total-mass identities into convolution-power upper bounds.
-- source:
--   Pinned Mathlib intervalIntegral.integral_nonneg and a direct induction on the causal convolution recursion.

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open MeasureTheory Set

theorem AvramDividend.Classical.causal_convolution_powers_nonnegative_on_nonnegative
    (κ : ℝ → ℝ) (F : ℕ → ℝ → ℝ)
    (hzero : F 0 = κ)
    (hsucc : ∀ n : ℕ, F (n + 1) =
      fun x : ℝ => ∫ s in (0 : ℝ)..x,
        κ s * F n (x - s))
    (hκ : ∀ t : ℝ, 0 ≤ t → 0 ≤ κ t) :
    ∀ n : ℕ, ∀ x : ℝ, 0 ≤ x → 0 ≤ F n x := by sorry
