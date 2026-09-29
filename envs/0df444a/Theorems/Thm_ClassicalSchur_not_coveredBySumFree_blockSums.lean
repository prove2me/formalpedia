-- Prove2me | Theorems.Thm_ClassicalSchur_not_coveredBySumFree_blockSums
-- name    : ClassicalSchur.not_coveredBySumFree_blockSums
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-26T21:19:52.532899+00:00
-- url     : https://prove2.me/theorems/b91919bb-2645-4d68-855c-1e91405ba4da
-- title:
--   No cover of $\hat A$ by $q \le k$ sumfree sets when $|A| \ge N - 1$ and $k$ colours force a monochromatic triangle on $N$ vertices
-- statement:
--   This is the cover form of Theorem 4.1 of Eliahou and Revuelta, with the Ramsey number replaced by any $N$ that has the monochromatic-triangle property.
--
--   Let $k, N \in \mathbb{N}$ and suppose that $\mathrm{TR}(k, N)$ holds: every colouring, with at most $k$ colours, of the pairs $x < y$ of a finite set of at least $N$ natural numbers has a monochromatic triangle. Let $A$ be a finite sequence of natural numbers with $N \le |A| + 1$, and let $q \le k$. Then the set $\hat A$ of block sums of $A$ (the sums of the nonempty runs of consecutive entries) is not covered by $q$ sumfree sets:
--
--   $$
--   \hat A \not\subseteq C_1 \cup \dots \cup C_q \qquad \text{for all sumfree sets } C_1, \dots, C_q \subseteq \mathbb{N}.
--   $$
--
--   Here a set is sumfree if it contains no $x, y, z$ with $x + y = z$, $x = y$ allowed.
--
--   Eliahou and Revuelta state Theorem 4.1 in this form in their introduction: if $\hat A$ is covered by $n$ sumfree sets, then $|A| \le R_n(3) - 2$. Combined with the pigeonhole bound $\mathrm{TR}(k, \rho(k))$, this lemma gives $\operatorname{sdeg}(\hat A) \ge k + 1$ whenever $|A| \ge \rho(k) - 1$.
--
--   **Formalization Note** The paper states Theorem 4.1 for sequences in an arbitrary abelian group; here the entries are natural numbers, and they are not required to be positive. The hypothesis $|A| \ge N - 1$ is written $N \le |A| + 1$. The case $q = 0$ is included; it states that $\hat A$ is nonempty.
-- source:
--   S. Eliahou and M. P. Revuelta, "The Schur degree of additive sets", Discrete Math. 344(5) (2021) 112332, https://doi.org/10.1016/j.disc.2021.112332 (preprint arXiv:2006.01502), Theorem 4.1, in the cover form stated in §1 (if Â can be covered by n sumfree parts, then |A| ≤ R_n(3) − 2). A. McKenna, "The Schur degree of block sums: L(4) = 16 and L(5) ≥ 49", Zenodo (2026), https://doi.org/10.5281/zenodo.22987189, §2 (Theorem 4.1 as quoted) and §7. Lean source: https://github.com/mysticflounder/schur-degree-block-sums/blob/v1.0.1/lean/ClassicalSchur/Ramsey.lean#L89-L127 (release v1.0.1, doi:10.5281/zenodo.22987688).

import Definitions.Def_ClassicalSchurBasic
import Definitions.Def_ClassicalSchurRamsey
import Mathlib

open ClassicalSchur

theorem ClassicalSchur.not_coveredBySumFree_blockSums {k N : ℕ} (hR : TriangleRamsey k N)
    {A : List ℕ} (hA : N ≤ A.length + 1) {q : ℕ} (hq : q ≤ k) :
    ¬ CoveredBySumFree (blockSums A) q := by sorry
