-- Prove2me | Theorems.Thm_AvramDividend_Classical_rightInterval_upper_before_horizon_grid_iff
-- name    : AvramDividend.Classical.rightInterval_upper_before_horizon_grid_iff
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T20:02:43.592278+00:00
-- url     : https://prove2.me/theorems/bab64f9e-0007-404f-81c1-2081939f1a77
-- title:
--   A right-persistent upper crossing has an inverse-natural grid witness before every horizon
-- statement:
--   Any nonnegative-time real-valued path whose strict upper crossings persist for some right interval has a crossing before horizon T exactly when it has a positive-denominator rational-grid crossing before T. This deterministic result applies to shifted paths of Lévy processes as well as their original trajectories.
-- source:
--   Generalises the Proved chat03_upper_before_horizon_countable_grid_iff by isolating its sole right-interval hypothesis; uses Proved NNReal grid-ceiling bracket and the pinned inverse-natural Archimedean lemma.

import Mathlib.Data.NNReal.Defs
import Theorems.Thm_AvramDividend_Classical_chat03_nnreal_grid_ceiling_bracket

open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.rightInterval_upper_before_horizon_grid_iff
    (g : ℝ≥0 → ℝ) (upper : ℝ)
    (hRight : ∀ s : ℝ≥0, upper < g s →
      ∃ u : ℝ≥0, s < u ∧
        ∀ r : ℝ≥0, s ≤ r → r < u → upper < g r)
    (T : ℝ≥0) :
    (∃ s : ℝ≥0, s < T ∧ upper < g s) ↔
    ∃ n : ℕ, 0 < n ∧ ∃ k : ℕ,
      (k : ℝ≥0) * (n : ℝ≥0)⁻¹ < T ∧
        upper < g ((k : ℝ≥0) * (n : ℝ≥0)⁻¹) := by sorry
