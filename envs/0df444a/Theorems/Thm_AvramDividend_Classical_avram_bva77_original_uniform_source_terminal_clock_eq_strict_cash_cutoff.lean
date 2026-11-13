-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva77_original_uniform_source_terminal_clock_eq_strict_cash_cutoff
-- name    : AvramDividend.Classical.avram_bva77_original_uniform_source_terminal_clock_eq_strict_cash_cutoff
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T21:00:19.589851+00:00
-- url     : https://prove2.me/theorems/244bba3b-358f-401e-bb9b-300f027ad0ef
-- title:
--   Original supplied uniform physical last clock equals strict discounted cash cut-off
-- statement:
--   For an arbitrary supplied ℝ≥0 physical grid u satisfying the original exact uniform-grid hypothesis of BVA63/BVA62, the final source-compensator evaluation time u(n,n+1) has real value T−T/(n+2) and is strictly before T for every row. This identifies the terminal M(u(n,n+1)) in Proved BVA75/BVA76 with the exact strict real cash cut-off in BVA63; no replacement grid, initial-reserve restrictions or finite jump assumptions.

import Mathlib
open Classical MeasureTheory Set Filter
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bva77_original_uniform_source_terminal_clock_eq_strict_cash_cutoff
    (T : ℝ) (hT : 0 < T) (u : ℕ → ℕ → ℝ≥0)
    (huniform : ∀ n i, (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2)) :
    ∀ n : ℕ,
      (u n (n + 1) : ℝ) = T - T / ((n : ℝ) + 2) ∧
      (u n (n + 1) : ℝ) < T := by sorry
