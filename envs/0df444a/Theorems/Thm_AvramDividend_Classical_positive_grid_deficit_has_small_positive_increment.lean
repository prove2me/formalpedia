-- Prove2me | Theorems.Thm_AvramDividend_Classical_positive_grid_deficit_has_small_positive_increment
-- name    : AvramDividend.Classical.positive_grid_deficit_has_small_positive_increment
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T13:23:26.355066+00:00
-- url     : https://prove2.me/theorems/7d6be355-1904-4719-9a5a-90bb9b202efe
-- title:
--   Positive finite-grid drift deficit forces a bounded positive increment
-- statement:
--   For a real-valued grid whose endpoint strictly exceeds its initial value, if every cell increment lies in [0,b], some cell increment is strictly positive and at most b. This is the finite-grid pathwise inclusion needed to bound actual stopped-survival drift deficits by a union of small positive increment events.
-- source:
--   Elementary finite-grid order argument in the finite-activity first-jump step of Avram, Palmowski and Pistorius (2007), section 3.3.

import Mathlib.Data.Real.Basic

theorem AvramDividend.Classical.positive_grid_deficit_has_small_positive_increment
    (D : ℕ → ℝ) (N : ℕ) (b : ℝ)
    (hPositive : LT.lt (D 0) (D N))
    (hBound : ∀ k : ℕ, LT.lt k N →
      LE.le 0 (D (k + 1) - D k) ∧ LE.le (D (k + 1) - D k) b) :
    ∃ k : ℕ, LT.lt k N ∧
      LT.lt 0 (D (k + 1) - D k) ∧ LE.le (D (k + 1) - D k) b := by sorry
