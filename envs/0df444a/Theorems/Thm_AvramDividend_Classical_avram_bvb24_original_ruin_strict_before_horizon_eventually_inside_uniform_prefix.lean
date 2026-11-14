-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb24_original_ruin_strict_before_horizon_eventually_inside_uniform_prefix
-- name    : AvramDividend.Classical.avram_bvb24_original_ruin_strict_before_horizon_eventually_inside_uniform_prefix
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T08:20:40.596195+00:00
-- url     : https://prove2.me/theorems/a91aa28a-1394-4ae8-807a-c27b284fbdf7
-- title:
--   Original uniform physical prefix eventually extends past any positive ruin time strictly before the observation horizon
-- statement:
--   Every finite actual ruin clock strictly before the original observation horizon lies inside all sufficiently fine original physical uniform-grid clipped prefixes. The prefix endpoint is exactly the original horizon minus horizon over the row index plus two. This separates strictly early ruin, where the original stopped cash and compensator see the full stopped source eventually, from ruin exactly at the horizon, where the endpoint strip needs a separate argument.
-- source:
--   Original BV finite-activity physical grid delta law in ed067740 and published positive-ruin strict-before-horizon child 56c6882c; pinned Mathlib const-div tendsto and Ioi neighbourhood lemmas.

import Mathlib
open Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb24_original_ruin_strict_before_horizon_eventually_inside_uniform_prefix
    (τ T : ℝ) (hτT : τ < T) :
    ∀ᶠ n : ℕ in atTop, τ < T - T / ((n : ℝ) + 2) := by sorry
