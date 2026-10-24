-- Prove2me | Theorems.Thm_AvramDividend_Classical_excursion_lintegral_limit_of_strict_subsequence
-- name    : AvramDividend.Classical.excursion_lintegral_limit_of_strict_subsequence
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T22:52:37.504297+00:00
-- url     : https://prove2.me/theorems/134d4d5d-7e6a-487d-94bb-5e8e812bb9c1
-- title:
--   Identify the Laplace-integral limit along a convergent subsequence
-- statement:
--   If the integrals of a nonnegative test function over a measure sequence converge to a specified extended nonnegative limit, and the integrals along a strictly increasing-index subsequence converge to the integral over a candidate limiting measure, then that candidate integral equals the specified limit.
-- source:
--   Unique limits in the Hausdorff ENNReal topology and convergence under a strictly monotone natural-number subsequence.

import Mathlib.MeasureTheory.Measure.Prokhorov

open MeasureTheory Filter Topology

theorem AvramDividend.Classical.excursion_lintegral_limit_of_strict_subsequence
    (β : ℕ → Measure ℝ) (μ : Measure ℝ) (g : ℝ → ENNReal)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (L : ENNReal)
    (hfull : Tendsto (fun n : ℕ => ∫⁻ x, g x ∂β n) atTop (𝓝 L))
    (hsub : Tendsto (fun n : ℕ => ∫⁻ x, g x ∂β (φ n)) atTop
      (𝓝 (∫⁻ x, g x ∂μ))) :
    (∫⁻ x, g x ∂μ) = L := by sorry
