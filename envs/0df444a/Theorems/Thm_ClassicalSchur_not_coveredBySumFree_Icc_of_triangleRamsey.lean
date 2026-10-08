-- Prove2me | Theorems.Thm_ClassicalSchur_not_coveredBySumFree_Icc_of_triangleRamsey
-- name    : ClassicalSchur.not_coveredBySumFree_Icc_of_triangleRamsey
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-10-04T00:29:46.173977+00:00
-- url     : https://prove2.me/theorems/213eb0cd-bd42-4a5e-9c9f-8f96355cc2e9
-- title:
--   Centred-interval Schur bound: if $R_k(3) \le r$, then $[1, 2(k+1)\lfloor (r-1)/2 \rfloor + 2]$ has no cover by $k+1$ sumfree sets
-- statement:
--   This is the centred-interval bound: a bound on the Schur number with $k + 1$ colours from a bound on the triangle Ramsey number with $k$ colours.
--
--   Let $k, r \in \mathbb{N}$ and suppose that $\mathrm{TR}(k, r)$ holds (Lean `TriangleRamsey k r`): every colouring with at most $k$ colours of the pairs $x < y$ of a finite set of at least $r$ naturals has a monochromatic triangle. For $k \ge 1$ this is the inequality $R_k(3) \le r$. A set $S \subseteq \mathbb{N}$ is **sumfree** if $x + y \notin S$ for all $x, y \in S$, the case $x = y$ included. Put $s = \lfloor (r - 1)/2 \rfloor$. Then the interval $[1, 2((k+1)s + 1)]$ is not covered by $k + 1$ sumfree sets:
--
--   $$
--   \Bigl[1,\ 2(k+1)\Bigl\lfloor \frac{r-1}{2} \Bigr\rfloor + 2\Bigr] \not\subseteq C_0 \cup C_1 \cup \dots \cup C_k \qquad \text{for all sumfree sets } C_0, \dots, C_k \subseteq \mathbb{N}.
--   $$
--
--   For the Schur number $S(k+1)$, the largest $N$ such that $[1, N]$ is partitioned into $k + 1$ sumfree sets, this gives: if $R_k(3) \le r$, then
--
--   $$
--   S(k+1) \le 2(k+1)\Bigl\lfloor \frac{r-1}{2} \Bigr\rfloor + 1 .
--   $$
--
--   For example, $R_2(3) = 6$ gives $S(3) \le 13$, which is the true value, and $R_5(3) \le 302$ gives $S(6) \le 1801$. The bound improves on $S(k+1) \le R_{k+1}(3) - 2$ combined with the recursive Ramsey bound only for even $r$. In the mission it fixes the frontier: with $r = 2t + 2$ and $m = (k+1)t$, it excludes $[1, 2m + 2]$, so $[1, 2m + 1]$ is the largest interval that this bound does not exclude for $k + 1$ colours. The other theorems describe a Schur colouring of that interval.
--
--   **Formalization Note.** The cover `CoveredBySumFree X (k + 1)` asks for $k + 1$ sumfree subsets of $\mathbb{N}$, indexed by `Fin (k + 1)`, whose union contains $X$; they need not be disjoint and need not lie in $X$. A partition into sumfree sets is a special case, so the bound on $S(k+1)$ follows. In `TriangleRamsey k r` the colours are natural numbers from any `Finset` of at most $k$ elements, and the pair colouring is a function $\mathbb{N} \to \mathbb{N} \to \mathbb{N}$ that is constrained only on the pairs $x < y$ of the vertex set; for $k \ge 1$ the statement is $R_k(3) \le r$. In $(r - 1)/2$ the subtraction is truncated and the division rounds down; for $r \le 1$ the hypothesis is false, so the truncation never matters. The case $k = 0$ is included: $\mathrm{TR}(0, r)$ holds for $r \ge 2$, and the conclusion says that $[1, 2s + 2]$ is not one sumfree set, which holds since $1 + 1 = 2$.
-- source:
--   A. McKenna, "S(6) ≤ 1801 if R₄(3) ≤ 61: a centred Schur bound and the structure at the frontier", Zenodo (2026), https://doi.org/10.5281/zenodo.23156099, Theorem 3.1 (if R_k(3) ≤ r, then [1, 2h] with h = (k + 1)⌊(r − 1)/2⌋ + 1 is not covered by k + 1 sumfree sets, so S(k + 1) ≤ 2(k + 1)⌊(r − 1)/2⌋ + 1), also stated as Theorem 1.1. Lean source: https://github.com/mysticflounder/schur-centred-bound/blob/v1.0.1/ClassicalSchur/SchurBound.lean#L71-L189 (release v1.0.1, doi:10.5281/zenodo.23156444).

import Definitions.Def_ClassicalSchurBasic
import Definitions.Def_ClassicalSchurRamsey
import Mathlib

open ClassicalSchur

theorem ClassicalSchur.not_coveredBySumFree_Icc_of_triangleRamsey {k r : ℕ} (hR : TriangleRamsey k r) :
    ¬ CoveredBySumFree (Set.Icc 1 (2 * ((k + 1) * ((r - 1) / 2) + 1))) (k + 1) := by sorry
