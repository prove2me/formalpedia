-- Prove2me | Theorems.Thm_Erdos287_dense_unit_sum_has_many_thirteen_term_runs
-- name    : Erdos287.dense_unit_sum_has_many_thirteen_term_runs
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T15:02:03.476893+00:00
-- url     : https://prove2.me/theorems/d9127b27-bef1-42b7-8b7c-ea97475eb2d2
-- title:
--   Many selected thirteen-term windows at ratio at most 2.952
-- statement:
--   Let $D\subseteq[m,M]$ have reciprocal sum one, where $1<m\le M$, $M\ge10^6$, and $1000M\le2952m$. Then there are more than $M/300$ distinct windows of thirteen consecutive integers all in $D$.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287.

import Mathlib

theorem Erdos287.dense_unit_sum_has_many_thirteen_term_runs (D : Finset ℕ) (m M : ℕ) (hm : 1 < m) (hmM : m ≤ M)
    (hD : D ⊆ Finset.Icc m M) (hsum : ∑ n ∈ D, (1 : ℝ) / n = 1)
    (hscale : 1000000 ≤ M) (hratio : 1000 * M ≤ 2952 * m) :
    let R := (Finset.Icc (m + 12) M).filter (fun n => ∀ i ∈ Finset.range 13, n - i ∈ D)
    M < 300 * R.card := by sorry
