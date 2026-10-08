-- Prove2me | Theorems.Thm_EmpiricalBernstein_SVP_corollary_9
-- name    : EmpiricalBernstein.SVP.corollary_9
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:41:28.893285+00:00
-- url     : https://prove2.me/theorems/2edd7c7f-477e-4317-83e6-893c664bb61f
-- title:
--   Corollary 9 — $\frac1n\sum_k(\frac1n\sum_j(x_k-x_j)^2)^2 \le \frac{1}{2n^2}\sum_{k,j}(x_k-x_j)^2$ on $[0,1]$
-- statement:
--   Let $x_1, \dots, x_n$ be points of $[0,1]$. Then
--
--   $$
--   \frac1n \sum_{k} \Big( \frac1n \sum_j (x_k - x_j)^2 \Big)^2 \le \frac{1}{2n^2} \sum_{k,j} (x_k - x_j)^2 ,
--   $$
--
--   all sums running over $1,\dots,n$.
--
--   This is Lemma 8 for $X, Y$ uniformly distributed on the points $x_1,\dots,x_n$; it gives the self-boundedness of $nV_n$ used in the proof of Theorem 10.
--
--   **Formalization Note** The paper writes $\{x_1,\dots,x_n\} \subset [0,1]$; the points form a list $x : \{1,\dots,n\} \to [0,1]$, so repetitions are allowed. The paper's index $k = 1,\dots,n$ is Lean's `k : Fin n`. At $n = 0$ both sides are $0$.
-- source:
--   Maurer, Pontil, Empirical Bernstein Bounds and Sample Variance Penalization, arXiv:0907.3740v1, Corollary 9, p. 4

import Mathlib

namespace EmpiricalBernstein.SVP

/-- Corollary 9 (arXiv:0907.3740v1, p. 4), for a list `x_1, …, x_n` of points of `[0, 1]`. -/
theorem corollary_9 {n : ℕ} (x : Fin n → ℝ) (hx : ∀ i, x i ∈ Set.Icc (0 : ℝ) 1) :
    (1 / (n : ℝ)) * ∑ k, ((1 / (n : ℝ)) * ∑ j, (x k - x j) ^ 2) ^ 2
      ≤ 1 / (2 * (n : ℝ) ^ 2) * ∑ k, ∑ j, (x k - x j) ^ 2 := by sorry

end EmpiricalBernstein.SVP
