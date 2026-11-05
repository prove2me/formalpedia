-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_prefix_adapted_from_endpoint_counts
-- name    : AvramDividend.Classical.avram_p4_g_isometry_prefix_adapted_from_endpoint_counts
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T17:50:15.710341+00:00
-- url     : https://prove2.me/theorems/fdab4d17-1d23-4e6d-bc4e-f3e73b594da7
-- title:
--   Original chronological predictable count prefixes automatically adapted
-- statement:
--   For the raw original filtration, if each physical marked jump count J_i is known measurably by the right endpoint and coefficient H_i is known at the left endpoint, compensated cell D_i=H_i(J_i−r_i) produces finite prefix sums strongly measurable at the current time. This removes original P4-G hPrefix once P2-E supplies count endpoint measurability.
-- source:
--   Pinned Mathlib Monotone/Filtration, StronglyMeasurable.sub/mul and Finset.sum. No Poisson, factorial or stopped martingale hypotheses.

import Mathlib
open MeasureTheory
open scoped NNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p4_g_isometry_prefix_adapted_from_endpoint_counts
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (grid : ℕ → ℝ≥0)
    (hGrid : ∀ i, grid i ≤ grid (i + 1))
    (H J D : ℕ → Ω → ℝ) (r : ℕ → ℝ)
    (hD : ∀ i ω, D i ω = H i ω * (J i ω - r i))
    (hH : ∀ i, StronglyMeasurable[𝓕 (grid i)] (H i))
    (hJ : ∀ i, StronglyMeasurable[𝓕 (grid (i + 1))] (J i))
    (n : ℕ) :
    StronglyMeasurable[𝓕 (grid n)]
      (fun ω => ∑ i ∈ Finset.range n, D i ω) := by sorry
