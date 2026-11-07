-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_measurable_deduplicated_weighted_mark_series
-- name    : AvramDividend.Classical.avram_bv_jump8_measurable_deduplicated_weighted_mark_series
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T00:23:48.148041+00:00
-- url     : https://prove2.me/theorems/37d36ef8-8cd7-45f8-9760-7f03c4ea6366
-- title:
--   Measurability of arbitrary Borel-weighted deduplicated jump candidate series
-- statement:
--   For any measurable candidate-time and mark family on coordinate-path space, the countable sum of arbitrary Borel nonnegative mark weights with a finite-horizon and first-appearance predicate is measurable, even when infinite. This is a mathematical child of the full càdlàg weighted-jump path-functional extension.
-- source:
--   Use the Proved original càdlàg measurable candidate selectors and marks 417d1996, 660f311b. The separate still-required equality between this series and actual intrinsic mapped count lintegral proves b50e56f2 when combined with this measurability.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.avram_bv_jump8_measurable_deduplicated_weighted_mark_series
    (time : ℕ → (ℝ≥0 → ℝ) → ℝ≥0)
    (mark : ℕ → (ℝ≥0 → ℝ) → ℝ)
    (hTime : ∀ k, Measurable (time k))
    (hMark : ∀ k, Measurable (mark k))
    (T : ℝ≥0) (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    Measurable (fun Y : ℝ≥0 → ℝ =>
      ∑' k : ℕ,
        if 0 < time k Y ∧ time k Y ≤ T ∧
            (∀ j : ℕ, j < k → time j Y ≠ time k Y)
        then g (mark k Y) else 0) := by sorry
