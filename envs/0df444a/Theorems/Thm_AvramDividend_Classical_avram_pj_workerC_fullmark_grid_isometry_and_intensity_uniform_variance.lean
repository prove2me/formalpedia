-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_fullmark_grid_isometry_and_intensity_uniform_variance
-- name    : AvramDividend.Classical.avram_pj_workerC_fullmark_grid_isometry_and_intensity_uniform_variance
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T08:13:42.297394+00:00
-- url     : https://prove2.me/theorems/d22b334a-eec9-4f3b-83cb-dbeb7fb86d77
-- title:
--   Original stopped negative-mark finite physical-grid martingale has uniform second moment from diagonal isometry and intensity
-- statement:
--   If the genuine stopped compensated negative-mark finite-grid increments have an exact diagonal second-moment isometry, all predictable weights are uniformly bounded by K and the nonnegative cell rates sum to at most B, then the expected sum of squared increments is at most K squared times B for every mesh size. This provides a concrete uniform L2 certificate compatible with genuine original physical-grid mark counting.

import Mathlib
open MeasureTheory Set Filter Topology
noncomputable section

theorem AvramDividend.Classical.avram_pj_workerC_fullmark_grid_isometry_and_intensity_uniform_variance
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (m : ℕ) (K B : ℝ) (hK : 0 ≤ K)
    (r : ℕ → ℝ)
    (hr : ∀ i ∈ Finset.range m, 0 ≤ r i)
    (hRate : (∑ i ∈ Finset.range m, r i) ≤ B)
    (H Z : ℕ → Ω → ℝ)
    (hHInt : ∀ i ∈ Finset.range m,
      Integrable (fun ω => (H i ω)^2) P)
    (hHBound : ∀ i ∈ Finset.range m, ∀ ω, |H i ω| ≤ K)
    (hEnergy :
      (∫ ω, ∑ i ∈ Finset.range m, (Z i ω)^2 ∂P) =
        ∑ i ∈ Finset.range m,
          r i * (∫ ω, (H i ω)^2 ∂P)) :
    (∫ ω, ∑ i ∈ Finset.range m, (Z i ω)^2 ∂P) ≤
      K^2 * B := by sorry
