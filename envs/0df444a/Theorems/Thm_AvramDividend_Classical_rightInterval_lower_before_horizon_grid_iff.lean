-- Prove2me | Theorems.Thm_AvramDividend_Classical_rightInterval_lower_before_horizon_grid_iff
-- name    : AvramDividend.Classical.rightInterval_lower_before_horizon_grid_iff
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T20:04:01.720343+00:00
-- url     : https://prove2.me/theorems/73caed33-aa2f-4773-90f7-76adae1eeb42
-- title:
--   A right-persistent lower crossing has an inverse-natural grid witness before every horizon
-- statement:
--   Any nonnegative-time real-valued path whose strict lower crossings persist over a short right interval has a crossing before horizon T exactly when some positive-denominator rational-grid sample crosses before T. This deterministic result applies to shifted right-continuous Lévy sample paths.
-- source:
--   Generalises the Proved chat03_lower_before_horizon_countable_grid_iff with an explicit right-interval hypothesis; reuses the proved grid-ceiling bracket and inverse-natural Archimedean lemma.

import Mathlib.Data.NNReal.Defs
import Theorems.Thm_AvramDividend_Classical_chat03_nnreal_grid_ceiling_bracket

open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.rightInterval_lower_before_horizon_grid_iff
    (g : ℝ≥0 → ℝ) (lower : ℝ)
    (hRight : ∀ s : ℝ≥0, g s < lower →
      ∃ u : ℝ≥0, s < u ∧
        ∀ r : ℝ≥0, s ≤ r → r < u → g r < lower)
    (T : ℝ≥0) :
    (∃ s : ℝ≥0, s < T ∧ g s < lower) ↔
    ∃ n : ℕ, 0 < n ∧ ∃ k : ℕ,
      (k : ℝ≥0) * (n : ℝ≥0)⁻¹ < T ∧
        g ((k : ℝ≥0) * (n : ℝ≥0)⁻¹) < lower := by sorry
