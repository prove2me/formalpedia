-- Prove2me | Theorems.Thm_Erdos287_reciprocal_budget_feasible_with_sparse_omissions
-- name    : Erdos287.reciprocal_budget_feasible_with_sparse_omissions
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T05:58:19.396684+00:00
-- url     : https://prove2.me/theorems/9f00164c-c97e-48db-9efd-a142feb19076
-- title:
--   Sparse exclusions can satisfy the reciprocal omission budget at large scales
-- statement:
--   Let $2\le l\le M$, let $H$ be a finite set of positions to omit, and assume $M\notin H$. Suppose $H$ contains no consecutive integers in $[l,M]$ and the reciprocal sum over $[l,M]\setminus H$ is at least one. Then there is a lower endpoint $m\in[l,M)$ outside $H$ for which the set $D=[m,M]\setminus H$ contains at least one of each consecutive pair in $[m,M]$, and
--
--   $$1\le \sum_{n\in D}\frac1n < 1+\frac1m,\qquad \sum_{n\in H\cap[m,M]}\frac1n\le\sum_{n=m}^M\frac1n-1.$$
--
--   This gives a feasible choice for the no-adjacent-omissions and one-sided omission-budget conditions used in the Erdős 287 residue certificates.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287. Feasibility of the spacing and reciprocal budget conditions used in local valuation certificates.

import Mathlib

theorem Erdos287.reciprocal_budget_feasible_with_sparse_omissions (lo M : ℕ) (hlo : 2 ≤ lo) (hlM : lo ≤ M)
    (H : Finset ℕ) (hM : M ∉ H)
    (hsep : ∀ n, lo ≤ n → n + 1 ≤ M → n ∈ H → n + 1 ∉ H)
    (hfull : (1 : ℚ) ≤ ∑ n ∈ Finset.Icc lo M \ H, (1 : ℚ) / n) :
    ∃ m, lo ≤ m ∧ m < M ∧ m ∉ H ∧
      (1 : ℚ) ≤ (∑ n ∈ Finset.Icc m M \ H, (1 : ℚ) / n) ∧
      (∑ n ∈ Finset.Icc m M \ H, (1 : ℚ) / n) < 1 + (1 : ℚ) / m ∧
      (∀ n, m ≤ n → n + 1 ≤ M → n ∈ Finset.Icc m M \ H ∨ n + 1 ∈ Finset.Icc m M \ H) ∧
      (∑ n ∈ Finset.Icc m M ∩ H, (1 : ℚ) / n) ≤ (∑ n ∈ Finset.Icc m M, (1 : ℚ) / n) - 1 := by sorry
