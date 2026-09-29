-- Prove2me | Theorems.Thm_ClassicalSchur_erL_four
-- name    : ClassicalSchur.erL_four
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-26T21:22:02.493663+00:00
-- url     : https://prove2.me/theorems/a8c917cb-3e1f-4a39-a0ba-eee73f76ebd4
-- title:
--   $L(4) = 16$ for the number $L(n)$ of Eliahou and Revuelta
-- statement:
--   This is the goal of the mission: the exact value of $L(4)$.
--
--   A set of natural numbers is *sumfree* if it contains no $x, y, z$ with $x + y = z$ ($x = y$ allowed). For a finite sequence $A = (a_1, \dots, a_N)$ of positive integers, let $\hat A = \{a_i + \dots + a_j : 1 \le i \le j \le N\}$ be its set of block sums, $\mu(A) = (a_1 + \dots + a_N)/N$ its average, and $\operatorname{sdeg}(\hat A)$ the least $n \ge 1$ such that $\hat A$ is covered by $n$ sumfree sets. For $n \ge 2$, Eliahou and Revuelta define $L(n)$ as the least positive integer $L$ such that every sequence $A$ of positive integers with $|A| = L$ and $\mu(A) \le n$ satisfies $\operatorname{sdeg}(\hat A) \ge n$. Then
--
--   $$
--   L(4) = 16 .
--   $$
--
--   Eliahou and Revuelta prove $S(n-1) + 1 \le L(n) \le R_{n-1}(3) - 1$ (Proposition 5.3), which gives $14 \le L(4) \le 16$ from the Schur number $S(3) = 13$ and the Ramsey number $R_3(3) = 17$. They conjecture $L(n) = S(n-1) + 1$ for all $n \ge 2$ (Conjecture 5.6), which at $n = 4$ states $L(4) = 14$. The value $16$ shows that Conjecture 5.6 does not hold at $n = 4$, and that at $n = 4$ the upper bound of Proposition 5.3 is attained.
--
--   **Formalization Note** $L(4)$ is `erL 4` of the Basic bundle, with the ambient set $\mathbb{N}$ and the Schur degree in the extended naturals. The defining set is nonempty for $n = 4$, so `erL 4` is its least element.
-- source:
--   S. Eliahou and M. P. Revuelta, "The Schur degree of additive sets", Discrete Math. 344(5) (2021) 112332, https://doi.org/10.1016/j.disc.2021.112332 (preprint arXiv:2006.01502), Definition 5.1 (the number L(n)); §5.1 (Proposition 5.3 implies 14 ≤ L(4) ≤ 16, and the conjecture L(4) = 14) and Conjecture 5.6. A. McKenna, "The Schur degree of block sums: L(4) = 16 and L(5) ≥ 49", Zenodo (2026), https://doi.org/10.5281/zenodo.22987189, Theorem 1.1 (proof in §3). Lean source: https://github.com/mysticflounder/schur-degree-block-sums/blob/v1.0.1/lean/ClassicalSchur/Values.lean#L77-L82 (release v1.0.1, doi:10.5281/zenodo.22987688).

import Definitions.Def_ClassicalSchurBasic
import Definitions.Def_ClassicalSchurRamsey
import Mathlib

open ClassicalSchur

theorem ClassicalSchur.erL_four : erL 4 = 16 := by sorry
