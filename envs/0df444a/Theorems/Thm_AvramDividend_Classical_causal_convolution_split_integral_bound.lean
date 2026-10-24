-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_convolution_split_integral_bound
-- name    : AvramDividend.Classical.causal_convolution_split_integral_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T12:15:19.65947+00:00
-- url     : https://prove2.me/theorems/b3cc5e00-bcf5-4335-9c4f-2160ff728e23
-- title:
--   Two-piece causal convolution bound from kernel and input local controls
-- statement:
--   Split a nonnegative causal convolution integral at an intermediate time u. If the reversed kernel is bounded above by A on the left interval, the input bounded above by B on the right, and their respective accumulated masses bounded by M and ρ, then the whole convolution is at most A*M+B*ρ. This is the exact analytic interval decomposition needed for the n²ρⁿ/x convolution-power induction.
-- source:
--   One-dimensional split for Gaussian C2 convolution-power pointwise induction; pinned Mathlib integral_add_adjacent_intervals and integral_mono_on_of_le_Ioo.

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open MeasureTheory Set

theorem AvramDividend.Classical.causal_convolution_split_integral_bound
    (κ F : ℝ → ℝ) (x u A B M ρ : ℝ)
    (h0u : 0 ≤ u) (hux : u ≤ x) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hleftInt : IntervalIntegrable
      (fun s : ℝ => κ (x - s) * F s) volume 0 u)
    (hrightInt : IntervalIntegrable
      (fun s : ℝ => κ (x - s) * F s) volume u x)
    (hFInt : IntervalIntegrable F volume 0 u)
    (hκInt : IntervalIntegrable (fun s : ℝ => κ (x - s)) volume u x)
    (hKleft : ∀ s ∈ Ioo (0 : ℝ) u, κ (x - s) ≤ A)
    (hFzero : ∀ s ∈ Ioo (0 : ℝ) u, 0 ≤ F s)
    (hFright : ∀ s ∈ Ioo u x, F s ≤ B)
    (hκzero : ∀ s ∈ Ioo u x, 0 ≤ κ (x - s))
    (hFmass : (∫ s in (0 : ℝ)..u, F s) ≤ M)
    (hκmass : (∫ s in u..x, κ (x - s)) ≤ ρ) :
    (∫ s in (0 : ℝ)..x, κ (x - s) * F s) ≤ A * M + B * ρ := by sorry
