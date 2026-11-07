-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_stopped_strict_precontact_grid_geometry
-- name    : AvramDividend.Classical.avram_bv_error7_original_stopped_strict_precontact_grid_geometry
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T23:23:54.520968+00:00
-- url     : https://prove2.me/theorems/0525155c-80ff-4e52-bf7a-3d990d8e448b
-- title:
--   Strict stopped precontact original physical grid retains the horizon and monotonicity
-- statement:
--   For an arbitrary sample-dependent stopping index of an ordered physical grid, excluding the last contact cell preserves the initial point, horizon and cell ordering. The stopping index zero case remains exact.
-- source:
--   Use the original stopped grid's monotonicity at k-1 if k>0 and its zero-clock endpoint otherwise. This is the exact geometric input for the original stopped BV positive Taylor error theorem to be applied to the strict prefix only.

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_error7_original_stopped_strict_precontact_grid_geometry
    {Ω : Type*} (u : ℕ → ℕ → ℝ≥0) (k : ℕ → Ω → ℕ) (T : ℝ≥0)
    (hGrid : ∀ m ω, u m 0 = 0 ∧ u m (k m ω) ≤ T ∧
      (∀ i, i < k m ω → u m i ≤ u m (i + 1))) :
    ∀ m ω, u m 0 = 0 ∧ u m (k m ω - 1) ≤ T ∧
      (∀ i, i < k m ω - 1 → u m i ≤ u m (i + 1)) := by sorry
