-- Prove2me | Theorems.Thm_Erdos287_opposite_parity_windows_count_short_even_runs
-- name    : Erdos287.opposite_parity_windows_count_short_even_runs
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T15:01:48.147812+00:00
-- url     : https://prove2.me/theorems/45e06a7e-7412-4083-9a3c-0c7e06303a83
-- title:
--   Counting short even selected runs from their enclosing windows
-- statement:
--   Let $H$ be a finite set of omissions with no consecutive positions. Suppose each window $[t,t+d]$, for $t$ in a finite set $W$, contains omissions of both parities. Let $R$ be the set of successive pairs of holes in $H$ with distance at most $d$ and a positive even number of interior positions. Then $|W|\le(d+1)|R|$.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287.

import Mathlib

theorem Erdos287.opposite_parity_windows_count_short_even_runs (H W : Finset ℕ) (d : ℕ) (hsep : ∀ n ∈ H, n + 1 ∉ H)
    (hW : ∀ t ∈ W, ∃ a ∈ H, ∃ b ∈ H, t ≤ a ∧ a < b ∧ b ≤ t + d ∧ a % 2 ≠ b % 2) :
    let runs := (H ×ˢ H).filter (fun xy => xy.1 + 3 ≤ xy.2 ∧ xy.2 - xy.1 ≤ d ∧
      Even (xy.2 - xy.1 - 1) ∧ ∀ n ∈ Finset.Ioo xy.1 xy.2, n ∉ H)
    W.card ≤ (d + 1) * runs.card := by sorry
