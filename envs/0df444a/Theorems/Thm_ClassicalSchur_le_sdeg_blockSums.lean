-- Prove2me | Theorems.Thm_ClassicalSchur_le_sdeg_blockSums
-- name    : ClassicalSchur.le_sdeg_blockSums
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-26T21:20:25.217989+00:00
-- url     : https://prove2.me/theorems/5bb25087-1c33-4d5c-92ae-7037b78d94b2
-- title:
--   ER Theorem 4.1 with the pigeonhole bound: $|A| \ge \rho(k) - 1$ implies $\operatorname{sdeg}(\hat A) \ge k + 1$
-- statement:
--   This is Theorem 4.1 of Eliahou and Revuelta for sequences of natural numbers, with the pigeonhole bound $\rho(k)$ in place of the Ramsey number $R_k(3)$.
--
--   Let $k \in \mathbb{N}$, let $\rho(0) = 2$ and $\rho(k+1) = (k+1)(\rho(k) - 1) + 2$, and let $A$ be a finite sequence of natural numbers with $\rho(k) \le |A| + 1$, that is, $|A| \ge \rho(k) - 1$. Let $\hat A$ be the set of block sums of $A$, and let $\operatorname{sdeg}(\hat A)$ be the least $n \ge 1$ such that $\hat A$ is covered by $n$ sumfree sets ($\infty$ if there is none). Then
--
--   $$
--   \operatorname{sdeg}(\hat A) \ge k + 1 .
--   $$
--
--   At $k = 3$, where $\rho(3) = 17 = R_3(3)$, it gives, for sequences of natural numbers, the case of Corollary 4.2 of the paper that every sequence of length at least $16$ has $\operatorname{sdeg}(\hat A) \ge 4$. It gives the property $P_4(16)$, and so the upper bound $L(4) \le 16$ of the goal. The lemma also shows that the set defining $L(n)$ is nonempty for every $n \ge 1$, and it is the source of the upper bound $L(k+1) \le \rho(k) - 1$.
--
--   **Formalization Note** The paper states Theorem 4.1 for sequences in an arbitrary abelian group, with $R_k(3)$; the Lean statement is for sequences in $\mathbb{N}$ (entries not required to be positive), with $\rho(k) \ge R_k(3)$ in place of $R_k(3)$. The inequality is taken in the extended naturals $\mathbb{N} \cup \{\infty\}$.
-- source:
--   S. Eliahou and M. P. Revuelta, "The Schur degree of additive sets", Discrete Math. 344(5) (2021) 112332, https://doi.org/10.1016/j.disc.2021.112332 (preprint arXiv:2006.01502), Theorem 4.1 (|A| ≥ R_n(3) − 1 implies sdeg(Â) ≥ n + 1) and Corollary 4.2. A. McKenna, "The Schur degree of block sums: L(4) = 16 and L(5) ≥ 49", Zenodo (2026), https://doi.org/10.5281/zenodo.22987189, §2 (Theorem 4.1 as quoted), §3 (proof of Theorem 1.1, the upper bound) and §7. Lean source: https://github.com/mysticflounder/schur-degree-block-sums/blob/v1.0.1/lean/ClassicalSchur/Ramsey.lean#L129-L133 (release v1.0.1, doi:10.5281/zenodo.22987688).

import Definitions.Def_ClassicalSchurBasic
import Definitions.Def_ClassicalSchurRamsey
import Mathlib

open ClassicalSchur

theorem ClassicalSchur.le_sdeg_blockSums {k : ℕ} {A : List ℕ} (hA : ramseyBound k ≤ A.length + 1) :
    ((k + 1 : ℕ) : ℕ∞) ≤ sdeg (blockSums A) := by sorry
