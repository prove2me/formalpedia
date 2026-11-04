-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_i_moment_compact_test_of_positive_band
-- name    : AvramDividend.Classical.avram_p2_i_moment_compact_test_of_positive_band
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:32:20.212426+00:00
-- url     : https://prove2.me/theorems/fbe2f483-db74-4209-a73f-7e3b2324cab1
-- title:
--   Moment convergence tests continuous positive-band functions even with irrelevant negative-side support
-- statement:
--   An enhanced finite-measure moment-to-continuous-test theorem. Assuming positive support for approximating measures, support of the finite limiting measure in [0,1], finite convergent ENNReal polynomial moments, and continuous g vanishing only on the nonnegative neighbourhood [0,δ] and [1,∞), conclude convergence of g integrals. The test may be nonzero on negative real arguments; its continuous positive cutoff agrees with g on the supports of all measures, then the previously Proved compact-test theorem applies. This matches the actual P2-B logarithmic test, which may have negative-side values due to Real.log.

import Mathlib
open MeasureTheory Filter Topology Set
open scoped ENNReal

theorem AvramDividend.Classical.avram_p2_i_moment_compact_test_of_positive_band
    {ι : Type*} (l : Filter ι)
    (μi : ι → Measure ℝ) (μ : Measure ℝ)
    (hpositive_i : ∀ i, ∀ᵐ z ∂μi i, 0 < z)
    (hunit_μ : ∀ᵐ z ∂μ, z ∈ Set.Icc (0 : ℝ) 1)
    (hmom_i_finite : ∀ i k,
      (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂μi i) ≠ ⊤)
    (hmom_μ_finite : ∀ k,
      (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂μ) ≠ ⊤)
    (hmom : ∀ k, Tendsto
      (fun i => ∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂μi i) l
      (nhds (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂μ)))
    (g : ℝ → ℝ) (hg : Continuous g)
    (δ : ℝ) (hδ : 0 < δ)
    (hzero_small : ∀ z : ℝ, 0 ≤ z → z ≤ δ → g z = 0)
    (hzero_upper : ∀ z : ℝ, 1 ≤ z → g z = 0) :
    Tendsto (fun i => ∫ z : ℝ, g z ∂μi i) l
      (nhds (∫ z : ℝ, g z ∂μ)) := by sorry
