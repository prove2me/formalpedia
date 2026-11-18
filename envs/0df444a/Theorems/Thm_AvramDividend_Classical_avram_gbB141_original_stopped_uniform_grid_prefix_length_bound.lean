-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB141_original_stopped_uniform_grid_prefix_length_bound
-- name    : AvramDividend.Classical.avram_gbB141_original_stopped_uniform_grid_prefix_length_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T19:00:59.743748+00:00
-- url     : https://prove2.me/theorems/9c55355b-7f1c-411b-9b04-223a0a3fe880
-- title:
--   Original strictly stopped physical-grid time-prefix length is at most horizon plus one cell
-- statement:
--   For every monotone original physical grid of constant nonnegative step Delta starting at zero, the sum of cell widths over exactly those mesh times strictly before the stopping horizon T is at most T+Delta. Use the Proved exact B108 stopping-prefix index and B63 finite-mask prefix identity, then bound its last crossing cell. This is the deterministic source-budget link required to control the upper-strip occupation drift correction from B139/B140 by the original stopped horizon.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB108_monotone_physical_grid_stop_mask_has_prefix_index
import Theorems.Thm_AvramDividend_Classical_avram_gbB63_original_finitegrid_prefix_mask_equals_short_range
open AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB141_original_stopped_uniform_grid_prefix_length_bound
    (s : ℕ → ℝ≥0) (hs : Monotone s) (hs0 : s 0 = 0)
    (Δ T : ℝ≥0) (hstep : ∀ i, s (i + 1) = s i + Δ)
    (m : ℕ) :
    (Finset.range (m + 1)).sum
      (fun i => if s i < T then (Δ : ℝ) else 0) ≤
      ((T + Δ : ℝ≥0) : ℝ) := by sorry
