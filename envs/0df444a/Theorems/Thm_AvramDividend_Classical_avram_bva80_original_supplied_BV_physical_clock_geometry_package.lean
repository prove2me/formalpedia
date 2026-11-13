-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva80_original_supplied_BV_physical_clock_geometry_package
-- name    : AvramDividend.Classical.avram_bva80_original_supplied_BV_physical_clock_geometry_package
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T21:22:12.85601+00:00
-- url     : https://prove2.me/theorems/3b10f7e2-e72b-4a52-b778-6073b420ad28
-- title:
--   BV source physical clock geometry package: zero origin, strict cells, strict terminal and horizon convergence
-- statement:
--   All clock premises for the original BV stopped C1 and compensated cash-grid lemma, derived for the supplied grid u rather than a replacement: zero initial node, strictly increasing cells, exact strict terminal T−T/(n+2), convergence to T.

import Mathlib
open Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva80_original_supplied_BV_physical_clock_geometry_package
    (T : ℝ) (hT : 0 < T) (u : ℕ → ℕ → ℝ≥0)
    (huniform : ∀ n i, (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2)) :
    (∀ n : ℕ, u n 0 = 0) ∧
    (∀ n i : ℕ, u n i < u n (i + 1)) ∧
    (∀ n : ℕ, (u n (n + 1) : ℝ) = T - T / ((n : ℝ) + 2) ∧
      (u n (n + 1) : ℝ) < T) ∧
    Tendsto (fun n : ℕ => (u n (n + 1) : ℝ)) atTop (𝓝 T) := by sorry
