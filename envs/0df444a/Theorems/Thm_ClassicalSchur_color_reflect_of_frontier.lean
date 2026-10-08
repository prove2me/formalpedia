-- Prove2me | Theorems.Thm_ClassicalSchur_color_reflect_of_frontier
-- name    : ClassicalSchur.color_reflect_of_frontier
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-10-04T00:30:22.407916+00:00
-- url     : https://prove2.me/theorems/24c1bfc7-d209-415d-b039-2052f5991336
-- title:
--   Forced reflection: $c(m+1-d) = c(m+1+d)$ for every $d \in [1, m]$ with $c(d) = c(m+1)$
-- statement:
--   This is the forced reflection about the point $m + 1$ at the frontier with $k + 2$ colours.
--
--   Let $k, u, t, m \in \mathbb{N}$ with $2t = (k+1)u$ and $m = (k+2)t$, and suppose that $\mathrm{TR}(k, u + 1)$ holds, that is, every colouring with at most $k$ colours of the pairs of a finite set of at least $u + 1$ naturals has a monochromatic triangle ($R_k(3) \le u + 1$). Let $c : \mathbb{N} \to \mathrm{Fin}(k+2)$ be a Schur colouring of $[1, 2m + 1]$ with $k + 2$ colours. Let $d \in \mathbb{N}$ with $1 \le d \le m$ and $c(d) = c(m+1)$. Then
--
--   $$
--   c(m + 1 - d) = c(m + 1 + d) .
--   $$
--
--   The reflection is asserted only for the $d$ that have the colour $c(m+1)$; by the balance theorem there are $t$ of them in $[1, m]$. It is not a property of every Schur colouring: the colouring of $[1, 5]$ with classes $\{1, 4\}$, $\{2, 3\}$, $\{5\}$ has $c(2) = c(3)$ but $c(1) \ne c(5)$, so it does not reflect about $3$ at $d = 2$. For six colours under $R_4(3) \le 61$ ($k = 4$, $u = 60$, $t = 150$, $m = 900$) the theorem gives $c(901 - d) = c(901 + d)$ for every $d \in [1, 900]$ with $c(d) = c(901)$. It is the step that makes every endpoint neighbourhood symmetric.
--
--   **Formalization Note.** The colouring is a function on all of $\mathbb{N}$, and `SchurColoring (2 * m + 1) c` constrains only its values on $[1, 2m+1]$; the case $x = y$ is included, so $c(2x) \ne c(x)$ for $1 \le x \le m$. In `TriangleRamsey k (u + 1)` the colours are natural numbers from any `Finset` of at most $k$ elements, and the pair colouring is a function $\mathbb{N} \to \mathbb{N} \to \mathbb{N}$ that is constrained only on the pairs $x < y$ of the vertex set; for $k \ge 1$ the statement is $R_k(3) \le u + 1$. For $k = 0$ the hypotheses force $u \ge 2$ and $m \ge 2$, and $[1, 2m+1] \supseteq [1, 5]$ has no Schur colouring with two colours, so the statement is vacuous there; the case $k = 1$ is not vacuous. $m + 1 - d$ is truncated subtraction on $\mathbb{N}$; since $d \le m$ it is the ordinary difference, and both $m + 1 - d$ and $m + 1 + d$ lie in $[1, 2m + 1]$. The statement is vacuous for $u = 0$, since $\mathrm{TR}(k, 1)$ is false. Example ($k = 1$, $u = 2$, $t = 2$, $m = 6$): for the Schur colouring of $[1, 13]$ with classes $\{1, 4, 7, 10, 13\}$, $\{2, 3, 11, 12\}$, $\{5, 6, 8, 9\}$, the $d \in [1, 6]$ with $c(d) = c(7)$ are $1$ and $4$, and indeed $c(6) = c(8)$ and $c(3) = c(11)$.
-- source:
--   A. McKenna, "S(6) ≤ 1801 if R₄(3) ≤ 61: a centred Schur bound and the structure at the frontier", Zenodo (2026), https://doi.org/10.5281/zenodo.23156099, Theorem 4.7 (§4.4, forced reflection). Lean source: https://github.com/mysticflounder/schur-centred-bound/blob/v1.0.1/ClassicalSchur/Frontier.lean#L422-L464 (release v1.0.1, doi:10.5281/zenodo.23156444).

import Definitions.Def_ClassicalSchurColoring
import Definitions.Def_ClassicalSchurRamsey
import Mathlib

open ClassicalSchur
open Finset

theorem ClassicalSchur.color_reflect_of_frontier {k u t m : ℕ} (hR : TriangleRamsey k (u + 1))
    (h2t : 2 * t = (k + 1) * u) (hm : m = (k + 2) * t) {c : ℕ → Fin (k + 2)}
    (hc : SchurColoring (2 * m + 1) c) {d : ℕ} (hd : 0 < d) (hdm : d ≤ m)
    (hq : c d = c (m + 1)) : c (m + 1 - d) = c (m + 1 + d) := by sorry
