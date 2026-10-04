-- Prove2me | Theorems.Thm_ClassicalSchur_triangleRamsey_succ
-- name    : ClassicalSchur.triangleRamsey_succ
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-10-04T00:29:34.066915+00:00
-- url     : https://prove2.me/theorems/e070b038-5057-41ad-9d72-3b4337e8dcc3
-- title:
--   Pigeonhole step for triangle Ramsey numbers: $R_k(3) \le N$ implies $R_{k+1}(3) \le (k+1)(N-1) + 2$
-- statement:
--   This is the classical recursive upper bound for the multicolour Ramsey numbers of triangles, in the form of the monochromatic-triangle property.
--
--   For $k, N \in \mathbb{N}$ write $\mathrm{TR}(k, N)$ (Lean `TriangleRamsey k N`) for the statement: for every finite set $V \subseteq \mathbb{N}$ with $|V| \ge N$, every set $K \subseteq \mathbb{N}$ of at most $k$ colours, and every colouring that gives each pair $x < y$ of elements of $V$ a colour $c(x, y) \in K$, there are $x < y < z$ in $V$ with $c(x, y) = c(y, z) = c(x, z)$. Write $R_k(3)$ for the least $N$ such that every colouring of the edges of the complete graph $K_N$ with $k$ colours has a monochromatic triangle. For $k \ge 1$, $\mathrm{TR}(k, N)$ holds when $N \ge R_k(3)$ and fails when $N < R_k(3)$; so it states $R_k(3) \le N$.
--
--   Let $k, N \in \mathbb{N}$. If $\mathrm{TR}(k, N)$ holds, then
--
--   $$
--   \mathrm{TR}\bigl(k + 1,\ (k + 1)(N - 1) + 2\bigr).
--   $$
--
--   In terms of Ramsey numbers, $R_{k+1}(3) \le (k+1)\bigl(R_k(3) - 1\bigr) + 2$, the bound of Greenwood and Gleason (1955, Theorem 6). In the mission it turns the hypothesis $R_4(3) \le 61$ into $R_5(3) \le 5 \cdot 60 + 2 = 302$; in general it turns $\mathrm{TR}(k, u + 1)$ with $2t = (k+1)u$ into $\mathrm{TR}(k + 1, 2t + 2)$, the Ramsey bound with one colour more that the frontier theorems need.
--
--   **Formalization Note.** Colours are natural numbers, and the colouring is a function $c : \mathbb{N} \to \mathbb{N} \to \mathbb{N}$ of which only the values $c(x, y)$ for $x < y$ in $V$ are constrained; "at most $k$ colours" means a `Finset` $K$ with $|K| \le k$. The subtraction $N - 1$ is truncated subtraction on $\mathbb{N}$, but no truncation occurs under the hypothesis: $\mathrm{TR}(k, 0)$ and $\mathrm{TR}(k, 1)$ are false for every $k$, since a set with at most one point has no triangle, so the hypothesis forces $N \ge 2$. The case $k = 0$ is included: $\mathrm{TR}(0, N)$ holds for every $N \ge 2$, because no pair can receive a colour from the empty set.
-- source:
--   Note "Schur bounds from triangle Ramsey bounds: the centred interval" (schur-numbers project, 2026-09-28, unpublished), sections "Statement" (the recursive bound R_k(3) ≤ k(R_{k−1}(3) − 1) + 2) and "Values" (R_5(3) ≤ 5·60 + 2 = 302 from R_4(3) ≤ 61); classical source: R. E. Greenwood and A. M. Gleason, "Combinatorial relations and chromatic graphs", Canad. J. Math. 7 (1955) 1–7, https://doi.org/10.4153/CJM-1955-001-4, Theorem 6 (t_{r+1} ≤ (r + 1)(t_r − 1) + 2). Lean proof not yet in a public repository.

import Definitions.Def_ClassicalSchurRamsey
import Mathlib

open ClassicalSchur

theorem ClassicalSchur.triangleRamsey_succ {k N : ℕ} (hR : TriangleRamsey k N) :
    TriangleRamsey (k + 1) ((k + 1) * (N - 1) + 2) := by sorry
