-- Prove2me | Theorems.Thm_ClassicalSchur_erL_five_bounds
-- name    : ClassicalSchur.erL_five_bounds
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-26T21:24:50.730464+00:00
-- url     : https://prove2.me/theorems/4f02af34-d426-49c2-b196-8413714a73d8
-- title:
--   $49 \le L(5) \le 65$ for the number $L(n)$ of Eliahou and Revuelta
-- statement:
--   This theorem bounds $L(5)$ from both sides.
--
--   Let $L(n)$ be the least positive integer $L$ such that every sequence $A$ of positive integers with $|A| = L$ and average $\mu(A) \le n$ has block sums $\hat A$ of Schur degree $\operatorname{sdeg}(\hat A) \ge n$ (Definition 5.1 of Eliahou and Revuelta). Then
--
--   $$
--   49 \le L(5) \le 65 .
--   $$
--
--   The statement has two parts:
--
--   1. the lower bound $49 \le L(5)$;
--   2. the upper bound $L(5) \le 65$.
--
--   At $n = 5$, Proposition 5.3 of the paper gives $L(5) \ge S(4) + 1 = 45$, where $S(4) = 44$ is the Schur number, and Conjecture 5.6 states $L(5) = 45$. The lower bound $49$ shows that Conjecture 5.6 does not hold at $n = 5$.
--
--   **Formalization Note** The note gives the upper bound $L(5) \le R_4(3) - 1 \le 61$ from the known bound $R_4(3) \le 62$. The Lean statement has the weaker bound $65$, from the pigeonhole bound $\rho(4) = 66$ of the Ramsey bundle, because the bound $R_4(3) \le 62$ is not formalized here. $L(5)$ is `erL 5` of the Basic bundle.
-- source:
--   S. Eliahou and M. P. Revuelta, "The Schur degree of additive sets", Discrete Math. 344(5) (2021) 112332, https://doi.org/10.1016/j.disc.2021.112332 (preprint arXiv:2006.01502), Definition 5.1, Proposition 5.3 and Conjecture 5.6, at n = 5 (the case n = 5 of Conjecture 5.6 is stated in §5.2). A. McKenna, "The Schur degree of block sums: L(4) = 16 and L(5) ≥ 49", Zenodo (2026), https://doi.org/10.5281/zenodo.22987189, Theorem 1.2 (proof in §5) and §7 (the formal upper bound 65). Lean source: https://github.com/mysticflounder/schur-degree-block-sums/blob/v1.0.1/lean/ClassicalSchur/Values.lean#L103-L111 (release v1.0.1, doi:10.5281/zenodo.22987688).

import Definitions.Def_ClassicalSchurBasic
import Definitions.Def_ClassicalSchurRamsey
import Definitions.Def_ClassicalSchurValues
import Mathlib

open ClassicalSchur

theorem ClassicalSchur.erL_five_bounds : 49 ≤ erL 5 ∧ erL 5 ≤ 65 := by sorry
