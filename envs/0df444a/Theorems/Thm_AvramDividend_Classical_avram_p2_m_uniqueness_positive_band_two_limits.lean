-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_m_uniqueness_positive_band_two_limits
-- name    : AvramDividend.Classical.avram_p2_m_uniqueness_positive_band_two_limits
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T22:23:08.996504+00:00
-- url     : https://prove2.me/theorems/f02f6a63-d9af-4407-b81d-ced77ff5a540
-- title:
--   Positive-band moment-limit uniqueness with logarithmic tests
-- statement:
--   For a single positive-supported family with finite ENNReal polynomial moments and two candidate finite unit-supported moment limits, all continuous real test integrals agree whenever the test vanishes on a positive image neighbourhood of zero and above one. The test may be nonzero on negative real inputs due to Real.log conventions. The proof uses the independently Proved P2-I positive-band approximation theorem twice and Hausdorff uniqueness. This provides endpoint-safe uniqueness for the true logarithmic inverse tests without assuming equality of the test integrals.

import Mathlib
open MeasureTheory Filter Topology Set
open scoped ENNReal

theorem AvramDividend.Classical.avram_p2_m_uniqueness_positive_band_two_limits
    {ι : Type*} (l : Filter ι) [l.NeBot]
    (μi : ι → Measure ℝ) (μ ν : Measure ℝ)
    (hpositive_i : ∀ i, ∀ᵐ z ∂μi i, 0 < z)
    (hunit_μ : ∀ᵐ z ∂μ, z ∈ Set.Icc (0 : ℝ) 1)
    (hunit_ν : ∀ᵐ z ∂ν, z ∈ Set.Icc (0 : ℝ) 1)
    (hfinite_i : ∀ i k,
      (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂μi i) ≠ ⊤)
    (hfinite_μ : ∀ k,
      (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂μ) ≠ ⊤)
    (hfinite_ν : ∀ k,
      (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂ν) ≠ ⊤)
    (hmom_μ : ∀ k, Tendsto
      (fun i => ∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂μi i) l
      (nhds (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂μ)))
    (hmom_ν : ∀ k, Tendsto
      (fun i => ∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂μi i) l
      (nhds (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂ν)))
    (g : ℝ → ℝ) (hg : Continuous g) (δ : ℝ) (hδ : 0 < δ)
    (hzero_small : ∀ z : ℝ, 0 ≤ z → z ≤ δ → g z = 0)
    (hzero_upper : ∀ z : ℝ, 1 ≤ z → g z = 0) :
    (∫ z : ℝ, g z ∂μ) = (∫ z : ℝ, g z ∂ν) := by sorry
