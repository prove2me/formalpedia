-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a29_compact_moving_base_translation_zero
-- name    : AvramDividend.Classical.avram_ga_a29_compact_moving_base_translation_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T09:26:37.268009+00:00
-- url     : https://prove2.me/theorems/3d83bcbd-8ae5-41d7-bee5-919f8816b07b
-- title:
--   Continuous compact value function is stable under vanishing Gaussian increment at moving base point
-- statement:
--   A continuous value function on an expanded compact reserve band has vanishing value difference when its evaluation base point moves arbitrarily inside the smaller compact band and its additive Gaussian spatial increment tends to zero. This is the missing deterministic bridge for the rho=n stop-straddling terminal cell in avram_ga_a28_terminal_horizon_ge_ae_zero.
-- source:
--   Root-connected original zero-jump Gaussian terminal cell ad246ef2; combine Proved original physical path limit 85dd6f23 with Proved compact pre-stop band e7de7c19 and the original clipped horizon identity fdfb0b39.

import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Set Filter
noncomputable section

theorem AvramDividend.Classical.avram_ga_a29_compact_moving_base_translation_zero
    (w : ℝ → ℝ) (a b : ℝ)
    (hw : ContinuousOn w (Set.Icc (a - 1) (b + 1)))
    (y δ : ℕ → ℝ) (hy : ∀ m, y m ∈ Set.Icc a b)
    (hδ : Tendsto δ atTop (nhds (0 : ℝ))) :
    Tendsto (fun m => w (y m + δ m) - w (y m))
      atTop (nhds (0 : ℝ)) := by sorry
