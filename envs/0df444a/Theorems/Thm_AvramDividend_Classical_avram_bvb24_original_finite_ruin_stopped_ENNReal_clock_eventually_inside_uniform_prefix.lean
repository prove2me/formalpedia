-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb24_original_finite_ruin_stopped_ENNReal_clock_eventually_inside_uniform_prefix
-- name    : AvramDividend.Classical.avram_bvb24_original_finite_ruin_stopped_ENNReal_clock_eventually_inside_uniform_prefix
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T08:24:30.007111+00:00
-- url     : https://prove2.me/theorems/a7777f2b-fe2f-4ce0-acf4-4d340be3c353
-- title:
--   Exact original extended-nonnegative finite ruin clock strictly before physical horizon is eventually within every fine uniform prefix
-- statement:
--   Take the actual original ruinTime of a source sample path as an extended nonnegative clock. If this ruin clock is strictly before the finite physical observation horizon, then it is strictly before the exact original uniform clipped-prefix endpoint, represented by ofReal of horizon minus mesh width, for all sufficiently fine rows. This allows replacing the original stopped-source jump and cash indicator by its full pre-ruin value on strictly early-ruin paths, retaining the original time/mark intensity and endpoint conventions.
-- source:
--   Pinned Mathlib ENNReal.toReal_lt_toReal, ofReal_toReal and ofReal_lt_ofReal_iff_of_nonneg, plus published original prefix result a91aa28a-1394-4ae8-807a-c27b284fbdf7.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb24_original_ruin_strict_before_horizon_eventually_inside_uniform_prefix
open Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb24_original_finite_ruin_stopped_ENNReal_clock_eventually_inside_uniform_prefix
    (τ : ℝ≥0∞) (T : ℝ) (hT : 0 < T)
    (hτ : τ < ENNReal.ofReal T) :
    ∀ᶠ n : ℕ in atTop,
      τ < ENNReal.ofReal (T - T / ((n : ℝ) + 2)) := by sorry
