-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b76_original_true_stop_single_crossing_cell
-- name    : AvramDividend.Classical.avram_b76_original_true_stop_single_crossing_cell
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T12:56:51.007737+00:00
-- url     : https://prove2.me/theorems/0b66c602-5fd9-4e51-8af2-3830958ef05f
-- title:
--   Original true clipped increasing physical mesh has at most one final stop-contact cell
-- statement:
--   For any strictly increasing original physical time grid and actual sample-path stopping clock, there is at most one grid cell that begins strictly before the clock and ends at that clock when both endpoints are stopped by minimum. Covers zero-clock vacuously. This separates the potentially unbounded ruin-crossing claim from compact pre-ruin interior cells.
-- source:
--   Original physical κ stopping-clock structure used in Avram Palmowski Pistorius 2007 Proposition 4(i); elementary min inequalities and strictly increasing NNReal time grid.

import Mathlib
open Set Filter
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_b76_original_true_stop_single_crossing_cell
    {Ω : Type*} (u : ℕ → ℝ≥0) (hu : StrictMono u)
    (κ : Ω → ℝ≥0) (ω : Ω) (i j : ℕ)
    (hiBefore : min (u i) (κ ω) < κ ω)
    (hiContact : min (u (i + 1)) (κ ω) = κ ω)
    (hjBefore : min (u j) (κ ω) < κ ω)
    (hjContact : min (u (j + 1)) (κ ω) = κ ω) :
    i = j := by sorry
