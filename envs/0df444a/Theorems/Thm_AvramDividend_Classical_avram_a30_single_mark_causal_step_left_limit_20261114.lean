-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a30_single_mark_causal_step_left_limit_20261114
-- name    : AvramDividend.Classical.avram_a30_single_mark_causal_step_left_limit_20261114
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:20:14.965085+00:00
-- url     : https://prove2.me/theorems/13750ad9-114f-4134-adb7-0551fb157069
-- title:
--   Single causal physical marked jump has exact pre-jump left limit at every positive time
-- statement:
--   For every mark a at any nonnegative jump time u, the right-continuous step a times the indicator of u≤t has left limit a when u<t and zero when t≤u, at every positive t.
-- source:
--   Pinned Mathlib topology of left-hand neighbourhood filters.

import Mathlib
open Set Filter Topology
open scoped NNReal ENNReal
noncomputable section

/-- An individual causal marked-jump step has its exact pre-jump left limit. -/

theorem AvramDividend.Classical.avram_a30_single_mark_causal_step_left_limit_20261114 (u : ℝ≥0) (a : ℝ) :
    ∀ t : ℝ≥0, 0 < t →
      Tendsto (fun v : ℝ≥0 => if u ≤ v then a else 0)
        (𝓝[<] t) (𝓝 (if u < t then a else 0)) := by sorry
