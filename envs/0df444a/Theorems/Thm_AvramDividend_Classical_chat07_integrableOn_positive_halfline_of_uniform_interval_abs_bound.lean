-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat07_integrableOn_positive_halfline_of_uniform_interval_abs_bound
-- name    : AvramDividend.Classical.chat07_integrableOn_positive_halfline_of_uniform_interval_abs_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T21:39:29.043991+00:00
-- url     : https://prove2.me/theorems/1a69e013-3346-4432-bed5-ac4c87904fa7
-- title:
--   Half-line integrability from uniform finite-interval absolute integral bounds
-- statement:
--   Let f:ℝ→ℝ have an interval integral on [0,n] for every natural n. If its absolute integrals over [0,n] are uniformly bounded by one real constant I, then f is Lebesgue integrable on (0,∞). This specialises Mathlib's improper-integral integrability criterion to natural-number exhaustions and is the exact final step required after the finite adjacent-unit scale derivative comparison.

import Mathlib.MeasureTheory.Integral.IntegralEqImproper

open MeasureTheory Set intervalIntegral

theorem AvramDividend.Classical.chat07_integrableOn_positive_halfline_of_uniform_interval_abs_bound
    (f : ℝ → ℝ) (I : ℝ)
    (hlocal : ∀ n : ℕ,
      IntervalIntegrable f volume 0 (n : ℝ))
    (hbounded : ∀ n : ℕ,
      (∫ x in (0 : ℝ)..(n : ℝ), |f x|) ≤ I) :
    IntegrableOn f (Ioi (0 : ℝ)) := by sorry
