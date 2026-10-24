-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_antitone_convolution_cutoff_split_mass_bound
-- name    : AvramDividend.Classical.causal_antitone_convolution_cutoff_split_mass_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T12:36:44.179273+00:00
-- url     : https://prove2.me/theorems/34039208-2a64-4a41-a724-8af84a54b292
-- title:
--   Antitone causal convolution bounded by cutoff kernel mass and split input controls
-- statement:
--   For an antitone real causal kernel and nonnegative input on the left convolution interval, a single kernel-mass bound ρ on (0,x-u] controls both the reversed kernel on the left and the total kernel mass on the right. If the input's left mass is ≤P and its right values are ≤B, then the whole convolution is bounded by ρP/(x-u)+Bρ. This is the reusable quantitative induction bridge towards n²ρⁿ/x.
-- source:
--   Combine three new proved helpers: reversed antitone cutoff mass, exact right-interval reversal, and two-piece causal convolution integral split.

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Theorems.Thm_AvramDividend_Classical_causal_convolution_split_integral_bound
import Theorems.Thm_AvramDividend_Classical_causal_antitone_reversed_kernel_cutoff_mass_bound
import Theorems.Thm_AvramDividend_Classical_causal_reversed_kernel_right_interval_mass_identity

open MeasureTheory Set

theorem AvramDividend.Classical.causal_antitone_convolution_cutoff_split_mass_bound
    (κ F : ℝ → ℝ) (x u ρ P B : ℝ)
    (h0u : 0 ≤ u) (hux : u ≤ x) (hxu : 0 < x - u)
    (hρ : 0 ≤ ρ) (hB : 0 ≤ B)
    (hanti : AntitoneOn κ (Ioi (0 : ℝ)))
    (hκcutInt : IntervalIntegrable κ volume 0 (x - u))
    (hκcutMass : (∫ t in (0 : ℝ)..(x - u), κ t) ≤ ρ)
    (hleftInt : IntervalIntegrable
      (fun s : ℝ => κ (x - s) * F s) volume 0 u)
    (hrightInt : IntervalIntegrable
      (fun s : ℝ => κ (x - s) * F s) volume u x)
    (hFInt : IntervalIntegrable F volume 0 u)
    (hκrightInt : IntervalIntegrable (fun s : ℝ => κ (x - s)) volume u x)
    (hFleft : ∀ s ∈ Ioo (0 : ℝ) u, 0 ≤ F s)
    (hFright : ∀ s ∈ Ioo u x, F s ≤ B)
    (hκright : ∀ s ∈ Ioo u x, 0 ≤ κ (x - s))
    (hFmass : (∫ s in (0 : ℝ)..u, F s) ≤ P) :
    (∫ s in (0 : ℝ)..x, κ (x - s) * F s) ≤
      (ρ / (x - u)) * P + B * ρ := by sorry
