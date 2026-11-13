-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB140_zero_level_from_shrinking_band_occupation
-- name    : AvramDividend.Classical.avram_gbB140_zero_level_from_shrinking_band_occupation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T09:28:33.981001+00:00
-- url     : https://prove2.me/theorems/b8fcc7f4-b9ad-40dc-b3c6-3925ea7372ba
-- title:
--   Zero level-set occupation from shrinking-band occupation limit
-- statement:
--   A nonnegative extended-real quantity bounded by every term of a sequence converging to zero must itself be zero. Apply this to the measure of an exact-level occupation set and the measures of shrinking occupation bands.
-- source:
--   Measure monotonicity and tendsto order bound.

import Mathlib
open Filter Topology
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB140_zero_level_from_shrinking_band_occupation
    (x : ℝ≥0∞) (u : ℕ → ℝ≥0∞)
    (hbound : ∀ k, x ≤ u k)
    (hlim : Tendsto u atTop (𝓝 (0 : ℝ≥0∞))) :
    x = 0 := by sorry
