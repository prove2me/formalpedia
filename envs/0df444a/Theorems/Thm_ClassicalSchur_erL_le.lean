-- Prove2me | Theorems.Thm_ClassicalSchur_erL_le
-- name    : ClassicalSchur.erL_le
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-26T21:20:57.948216+00:00
-- url     : https://prove2.me/theorems/d3c71524-b926-4557-bef2-e2d51dc49c3d
-- title:
--   Upper bound $L(k+1) \le \rho(k) - 1$ (ER Proposition 5.3 with the pigeonhole bound)
-- statement:
--   This is the upper bound of Proposition 5.3 of Eliahou and Revuelta, with the pigeonhole bound $\rho$ in place of the Ramsey numbers.
--
--   Let $L(n)$ be the least positive integer $L$ such that every sequence $A$ of positive integers with $|A| = L$ and average $\mu(A) \le n$ has block sums of Schur degree $\operatorname{sdeg}(\hat A) \ge n$. Let $\rho(0) = 2$ and $\rho(k+1) = (k+1)(\rho(k) - 1) + 2$. Then for every $k \in \mathbb{N}$,
--
--   $$
--   L(k+1) \le \rho(k) - 1 .
--   $$
--
--   The values $\rho(1) - 1, \dots, \rho(4) - 1 = 2, 5, 16, 65$ give $L(2) \le 2$, $L(3) \le 5$, $L(4) \le 16$ and $L(5) \le 65$. The first two agree with the values $L(2) = 2$ and $L(3) = 5$ of the paper, and the last is the upper half of the bounds $49 \le L(5) \le 65$ of the mission.
--
--   **Formalization Note** The paper states $L(n) \le R_{n-1}(3) - 1$ for $n \ge 2$; the Lean statement has $n = k + 1$ for every $k \ge 0$, and $\rho(k) \ge R_k(3)$ in place of $R_k(3)$. At $k = 4$ it gives $65$, while the known bound $R_4(3) \le 62$ with Proposition 5.3 gives $L(5) \le 61$. The subtraction is ordinary subtraction because $\rho(k) \ge 2$.
-- source:
--   S. Eliahou and M. P. Revuelta, "The Schur degree of additive sets", Discrete Math. 344(5) (2021) 112332, https://doi.org/10.1016/j.disc.2021.112332 (preprint arXiv:2006.01502), Proposition 5.3 (upper bound L(n) ≤ R_{n−1}(3) − 1). A. McKenna, "The Schur degree of block sums: L(4) = 16 and L(5) ≥ 49", Zenodo (2026), https://doi.org/10.5281/zenodo.22987189, §2 (Proposition 5.3 as quoted) and §7. Lean source: https://github.com/mysticflounder/schur-degree-block-sums/blob/v1.0.1/lean/ClassicalSchur/Ramsey.lean#L152-L156 (release v1.0.1, doi:10.5281/zenodo.22987688).

import Definitions.Def_ClassicalSchurBasic
import Definitions.Def_ClassicalSchurRamsey
import Mathlib

open ClassicalSchur

theorem ClassicalSchur.erL_le (k : ℕ) : erL (k + 1) ≤ ramseyBound k - 1 := by sorry
