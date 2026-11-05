-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_m_uniqueness_compact_unit_moment_test_limit
-- name    : AvramDividend.Classical.avram_p2_m_uniqueness_compact_unit_moment_test_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T11:54:16.675063+00:00
-- url     : https://prove2.me/theorems/5a1a0ab7-f1ad-4a11-bd30-dd077eb8f426
-- title:
--   Compact positive finite-measure moment limits imply continuous positive-band test limits
-- statement:
--   Consider finite positive Borel measures supported in the open unit interval and a finite candidate limit supported on the closed unit interval. If every nonnegative integer Hausdorff moment converges along a filter, then the integrals of any continuous test function vanishing near zero and at or above one converge to its integral under the candidate. Finite total mass and compact support already guarantee finiteness of every moment; no separate moment-integrability assumption is needed. This is the compact-image analytic step needed before inverse exponential transport of Lévy negative-mark bands.

import Mathlib
open MeasureTheory Filter Topology Set
open scoped ENNReal

theorem AvramDividend.Classical.avram_p2_m_uniqueness_compact_unit_moment_test_limit
    {ι : Type*} (l : Filter ι)
    (μi : ι → Measure ℝ) (μ : Measure ℝ)
    (hfinite_i : ∀ i, (μi i) Set.univ < ⊤)
    (hfinite_μ : μ Set.univ < ⊤)
    (hopen_i : ∀ i, ∀ᵐ z ∂μi i, z ∈ Set.Ioo (0 : ℝ) 1)
    (hunit_μ : ∀ᵐ z ∂μ, z ∈ Set.Icc (0 : ℝ) 1)
    (hmom : ∀ k, Tendsto
      (fun i => ∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂μi i) l
      (nhds (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂μ)))
    (g : ℝ → ℝ) (hg : Continuous g)
    (δ : ℝ) (hδ : 0 < δ)
    (hzero_small : ∀ z : ℝ, 0 ≤ z → z ≤ δ → g z = 0)
    (hzero_upper : ∀ z : ℝ, 1 ≤ z → g z = 0) :
    Tendsto (fun i => ∫ z : ℝ, g z ∂μi i) l
      (nhds (∫ z : ℝ, g z ∂μ)) := by sorry
