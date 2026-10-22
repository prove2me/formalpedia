-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_time_difference_support
-- name    : AvramDividend.Classical.gaussian_double_tail_time_difference_support
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T20:46:00.941251+00:00
-- url     : https://prove2.me/theorems/f12fe2d3-13c7-436d-ac66-d88882559228
-- title:
--   Positive-tail support of Gaussian double-tail time differences
-- statement:
--   The difference of two Gaussian Esscher double-tail atoms at times s,t bounded below by epsilon vanishes for jumps smaller than epsilon. Therefore its whole-measure L1 integral equals the same integral restricted to the fixed positive jump tail. This is valid even for infinite-activity Levy measures and prepares the global time-Lipschitz estimate.
-- source:
--   Pure support/indicator identity using strict-order conditions and pinned lintegral_indicator.

import Mathlib
open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.gaussian_double_tail_time_difference_support
    (μ : Measure ℝ) (ε φ s t : ℝ)
    (hs : ε ≤ s) (ht : ε ≤ t) :
    (∫⁻ z : ℝ, ENNReal.ofReal
      (|(if 0 < t ∧ t < z then (z - t) * Real.exp (-φ * z) else 0) -
        (if 0 < s ∧ s < z then (z - s) * Real.exp (-φ * z) else 0)|) ∂μ) =
    (∫⁻ z in Ici ε, ENNReal.ofReal
      (|(if 0 < t ∧ t < z then (z - t) * Real.exp (-φ * z) else 0) -
        (if 0 < s ∧ s < z then (z - s) * Real.exp (-φ * z) else 0)|) ∂μ) := by sorry
