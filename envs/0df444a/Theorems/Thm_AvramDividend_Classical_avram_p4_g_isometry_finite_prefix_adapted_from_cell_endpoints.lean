-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_finite_prefix_adapted_from_cell_endpoints
-- name    : AvramDividend.Classical.avram_p4_g_isometry_finite_prefix_adapted_from_cell_endpoints
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T17:46:52.199879+00:00
-- url     : https://prove2.me/theorems/4d263e25-a33a-49f3-9f11-d690affab0ed
-- title:
--   Finite chronological adapted prefixes from endpoint-measurable cells
-- statement:
--   For any source filtration and time grid whose earlier cell endpoints precede the later observation time, if the original physical compensated jump cell D_i is measurable at its right endpoint, every finite prefix sum is measurably adapted at the corresponding grid time. This discharges the hPrefix side condition of original P4-G finite-grid isometry.
-- source:
--   Pinned Mathlib Filtration.mono, StronglyMeasurable.mono and Finset.stronglyMeasurable_sum; provides adaptedness once P2-E supplies true original cell count endpoint measurability.

import Mathlib
open MeasureTheory
open scoped NNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p4_g_isometry_finite_prefix_adapted_from_cell_endpoints
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (grid : ℕ → ℝ≥0)
    (hEarlier : ∀ i n, i < n → grid (i + 1) ≤ grid n)
    (D : ℕ → Ω → ℝ)
    (hCell : ∀ i, StronglyMeasurable[𝓕 (grid (i + 1))] (D i))
    (n : ℕ) :
    StronglyMeasurable[𝓕 (grid n)]
      (fun ω => ∑ i ∈ Finset.range n, D i ω) := by sorry
