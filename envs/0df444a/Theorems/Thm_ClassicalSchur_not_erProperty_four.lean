-- Prove2me | Theorems.Thm_ClassicalSchur_not_erProperty_four
-- name    : ClassicalSchur.not_erProperty_four
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-26T21:21:36.648487+00:00
-- url     : https://prove2.me/theorems/0eedb55a-4a17-4f3f-a808-743ad77e37d3
-- title:
--   The property defining $L(4)$ fails at every length $1 \le L \le 15$
-- statement:
--   This theorem is the lower half of $L(4) = 16$.
--
--   For a natural number $L$, let $P_4(L)$ be the property of Definition 5.1 of Eliahou and Revuelta at $n = 4$: every sequence $A$ of positive integers with $|A| = L$ and average $\mu(A) \le 4$ has $\operatorname{sdeg}(\hat A) \ge 4$. Here $\hat A$ is the set of sums of the nonempty runs of consecutive entries of $A$, and $\operatorname{sdeg}(X)$ is the least $n \ge 1$ such that $X$ is covered by $n$ sumfree sets ($\infty$ if there is none). Then
--
--   $$
--   \neg P_4(L) \qquad \text{for every } L \text{ with } 1 \le L \le 15 .
--   $$
--
--   That is, for each such $L$ there is a sequence $A$ of $L$ positive integers with $\mu(A) \le 4$ and $\operatorname{sdeg}(\hat A) \le 3$.
--
--   Since $L(4)$ is the least positive $L$ such that $P_4(L)$ holds, this gives $L(4) \ge 16$. The case $L = 14$ answers, in the negative, the question that Eliahou and Revuelta ask after Conjecture 5.6: whether every sequence of positive integers of length $14$ and average at most $4$ has $\operatorname{sdeg}(\hat A) \ge 4$.
--
--   **Formalization Note** $P_4(L)$ is `ERProperty 4 L` of the Basic bundle: the average is computed in $\mathbb{Q}$, and the Schur degree in the extended naturals, where $\operatorname{sdeg}(\hat A) \le 3$ is the negation of $\operatorname{sdeg}(\hat A) \ge 4$.
-- source:
--   S. Eliahou and M. P. Revuelta, "The Schur degree of additive sets", Discrete Math. 344(5) (2021) 112332, https://doi.org/10.1016/j.disc.2021.112332 (preprint arXiv:2006.01502), Definition 5.1 (the property at n = 4); the case L = 14 is the question stated after Conjecture 5.6 in §5.1. A. McKenna, "The Schur degree of block sums: L(4) = 16 and L(5) ≥ 49", Zenodo (2026), https://doi.org/10.5281/zenodo.22987189, §3 (proof of Theorem 1.1, the lower bound). Lean source: https://github.com/mysticflounder/schur-degree-block-sums/blob/v1.0.1/lean/ClassicalSchur/Values.lean#L54-L71 (release v1.0.1, doi:10.5281/zenodo.22987688).

import Definitions.Def_ClassicalSchurBasic
import Definitions.Def_ClassicalSchurValues
import Mathlib

open ClassicalSchur

theorem ClassicalSchur.not_erProperty_four {L : ℕ} (h0 : 0 < L) (hL : L ≤ 15) : ¬ ERProperty 4 L := by sorry
