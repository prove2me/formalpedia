-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_renewal_partial_sum_truncated_mass_bound
-- name    : AvramDividend.Classical.causal_renewal_partial_sum_truncated_mass_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T10:06:57.867355+00:00
-- url     : https://prove2.me/theorems/733befcc-b1c6-4cfa-8bbe-2512dcdf562e
-- title:
--   Geometric upper bound for the integrated finite renewal-power sums
-- statement:
--   If each causal renewal convolution power is integrable on the positive half-line and its truncated mass is bounded by a geometric power, then the integral of every finite sum of powers is bounded by the corresponding finite geometric sum. This supplies the finite-approximation bound needed to apply monotone convergence at time zero.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open MeasureTheory Set

theorem AvramDividend.Classical.causal_renewal_partial_sum_truncated_mass_bound
    (F : ℕ → ℝ → ℝ) (ρ b : ℝ)
    (hFi : ∀ n : ℕ, IntegrableOn (F n) (Ioi (0 : ℝ)) volume)
    (hbound : ∀ n : ℕ,
      (∫ t in Ioc (0 : ℝ) b, F n t ∂volume) ≤ ρ ^ (n + 1))
    (s : Finset ℕ) :
    (∫ t in Ioc (0 : ℝ) b, ∑ n ∈ s, F n t ∂volume) ≤
      ∑ n ∈ s, ρ ^ (n + 1) := by sorry
