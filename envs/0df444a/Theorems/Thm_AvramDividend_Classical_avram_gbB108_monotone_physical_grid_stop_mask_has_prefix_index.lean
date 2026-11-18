-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB108_monotone_physical_grid_stop_mask_has_prefix_index
-- name    : AvramDividend.Classical.avram_gbB108_monotone_physical_grid_stop_mask_has_prefix_index
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T17:08:29.045485+00:00
-- url     : https://prove2.me/theorems/ed243b1c-2eb2-4c65-a547-a9c15c382b9f
-- title:
--   Every monotone physical grid has a finite first-horizon prefix cutoff
-- statement:
--   For every monotone sequence of nonnegative physical-grid times and every stopping horizon T, there is a natural number k at most m+1 such that among the first m+1 mesh points, s_i<T holds exactly when i<k. This is the deterministic stopped-grid indexing lemma needed to invoke the Proved B63/B64 prefix-noise certificate at the actual cutoff.

import Mathlib
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB108_monotone_physical_grid_stop_mask_has_prefix_index
    (s : ℕ → ℝ≥0) (hs : Monotone s) (T : ℝ≥0) (m : ℕ) :
    ∃ k : ℕ, k ≤ m + 1 ∧
      ∀ i : ℕ, i < m + 1 → (s i < T ↔ i < k) := by sorry
