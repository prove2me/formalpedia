-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_locmoll_compact_cutoff
-- name    : AvramDividend.Classical.avram_locmoll_compact_cutoff
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T21:41:50.031802+00:00
-- url     : https://prove2.me/theorems/d7e2a2a9-9d09-4b82-b610-f1358dc2560b
-- title:
--   A C2 function on an open set has a compact smooth extension agreeing on an interior ball
-- statement:
--   A C2 function on an open set has a compact smooth extension agreeing on an interior ball
-- source:
--   Avram Proposition 4(i), child of 06cb2549-7f74-48bc-a6ba-0890037b26d6

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology Convolution
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_locmoll_compact_cutoff
    (w : ℝ → ℝ) (s : Set ℝ) (hs : IsOpen s)
    (hw : ContDiffOn ℝ 2 w s) (c r R : ℝ)
    (hr : 0 < r) (hrR : r < R)
    (hR : Metric.closedBall c R ⊆ s) :
    ∃ F : ℝ → ℝ, ContDiff ℝ 2 F ∧ HasCompactSupport F ∧
      EqOn F w (Metric.ball c r) := by sorry
