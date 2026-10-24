-- Prove2me | Theorems.Thm_AvramDividend_Classical_finite_grid_lower_barrier_eventually_irrelevant_corrected
-- name    : AvramDividend.Classical.finite_grid_lower_barrier_eventually_irrelevant_corrected
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T07:08:27.125394+00:00
-- url     : https://prove2.me/theorems/6b41dffa-34ef-4de3-afaf-e91fc61e6984
-- title:
--   Finite-grid lower barrier is eventually irrelevant to each two-sided strict exit test (correct implication scope)
-- statement:
--   For any finite sequence f(0),...,f(m) and upper threshold z, choose a natural-number lower barrier magnitude N large enough that all observations exceed −N. Then for any n≥N and k≤m, the statement [f(k)>z OR f(k)<−n] is equivalent to f(k)>z. Crucially the bounded-index premise k≤m scopes over the entire biconditional, not only over the left operand. This is the correct finite-path exhaustion lemma needed to reduce two-sided finite-grid upper-exit stopping to one-sided finite-grid stopping.
-- source:
--   Corrected version of archived initial finite-grid draft; private remote compiler exposed implication/biconditional precedence error.

import Mathlib

theorem AvramDividend.Classical.finite_grid_lower_barrier_eventually_irrelevant_corrected
    (f : ℕ → ℝ) (z : ℝ) (m : ℕ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ k : ℕ, k ≤ m →
      ((z < f k ∨ f k < -(n : ℝ)) ↔ z < f k) := by sorry
