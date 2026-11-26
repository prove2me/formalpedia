-- Prove2me | Theorems.Thm_Erdos287_distinct_cofactor_intervals_form_chain
-- name    : Erdos287.distinct_cofactor_intervals_form_chain
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T13:23:18.953044+00:00
-- url     : https://prove2.me/theorems/9777a87e-03d2-4fe4-a68b-06a890f03eb4
-- title:
--   Linear bound on distinct cofactor intervals at a fixed scale
-- statement:
--   Fix $m\le M$ in the natural numbers. Let $P$ be a finite set of positive integers $p$ such that $\lfloor M/p\rfloor\le B$. Then the endpoint pairs $(\lfloor(m-1)/p\rfloor+1,\lfloor M/p\rfloor)$ take at most $2B+1$ distinct values.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287.

import Mathlib

theorem Erdos287.distinct_cofactor_intervals_form_chain (P : Finset ℕ) (m M B : ℕ) (hmM : m ≤ M)
    (hP : ∀ p ∈ P, 0 < p ∧ M / p ≤ B) :
    (P.image (fun p => ((m - 1) / p + 1, M / p))).card ≤ 2 * B + 1 := by sorry
