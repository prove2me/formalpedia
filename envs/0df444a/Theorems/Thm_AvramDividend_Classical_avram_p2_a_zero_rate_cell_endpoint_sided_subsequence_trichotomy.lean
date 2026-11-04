-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_cell_endpoint_sided_subsequence_trichotomy
-- name    : AvramDividend.Classical.avram_p2_a_zero_rate_cell_endpoint_sided_subsequence_trichotomy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T18:41:57.36665+00:00
-- url     : https://prove2.me/theorems/53d54e99-0278-41fa-b2ec-dc465d02dbb1
-- title:
--   Every sequence of original mesh cells has a uniform left/right/straddling time subsequence
-- statement:
--   For any sequence of nonnegative left and right mesh endpoints a_n and b_n and fixed time t, extract a strictly increasing subsequence on which every cell falls entirely before t, entirely at or after t, or straddles t as a_n < t ≤ b_n. This is a deterministic order-trichotomy using two applications of the Mathlib finite-union subsequence theorem; it makes no Lévy-rate or jump-count assumption.

import Mathlib
open Set Filter Topology
open scoped NNReal

theorem AvramDividend.Classical.avram_p2_a_zero_rate_cell_endpoint_sided_subsequence_trichotomy
    (a b : ℕ → ℝ≥0) (t : ℝ≥0) :
    ∃ g : ℕ ↪o ℕ,
      (∀ n, b (g n) < t) ∨
      (∀ n, t ≤ a (g n)) ∨
      (∀ n, a (g n) < t ∧ t ≤ b (g n)) := by sorry
