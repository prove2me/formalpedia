-- Prove2me | Theorems.Thm_ClassicalSchur_card_filter_Icc_eq_of_frontier
-- name    : ClassicalSchur.card_filter_Icc_eq_of_frontier
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-10-04T00:29:53.319812+00:00
-- url     : https://prove2.me/theorems/606d4619-8ffd-45aa-9cba-1e8e5bc48a2f
-- title:
--   Balanced colour classes: at the frontier of the centred bound each of the $k+1$ colours occurs $t$ times in $[1, m]$
-- statement:
--   This is the balance of colour classes at the frontier of the centred bound.
--
--   Let $k, t, m \in \mathbb{N}$ with $m = (k+1)t$, and suppose that $\mathrm{TR}(k, 2t + 2)$ holds (Lean `TriangleRamsey k (2 * t + 2)`): every colouring with at most $k$ colours of the pairs of a finite set of at least $2t + 2$ naturals has a monochromatic triangle, that is, $R_k(3) \le 2t + 2$. Let $c : \mathbb{N} \to \mathrm{Fin}(k+1)$ be a Schur colouring of $[1, 2m + 1]$ with $k + 1$ colours: there are no $x, y \ge 1$ with $x + y \le 2m + 1$ and $c(x) = c(y) = c(x + y)$. Then for every colour $j \in \mathrm{Fin}(k+1)$,
--
--   $$
--   \bigl|\{\, d \in [1, m] : c(d) = j \,\}\bigr| = t .
--   $$
--
--   With $r = 2t + 2$ the centred bound excludes Schur colourings of $[1, 2m + 2]$ with $k + 1$ colours, so $[1, 2m + 1]$ is the frontier interval. The theorem says that at the frontier the first half $[1, m]$ is split evenly among the $k + 1$ colours. The frontier theorems apply it with $k + 1$ in place of $k$ (so $k + 2$ colours, $\mathrm{TR}(k+1, 2t+2)$ and $m = (k+2)t$) to the colour $c(m+1)$. For six colours the goal applies it with $k = 5$, $t = 150$, $m = 900$ and $\mathrm{TR}(5, 302)$, which follows from $R_4(3) \le 61$ by the pigeonhole step; it gives that each colour occurs $150$ times in $[1, 900]$.
--
--   **Formalization Note.** Colours are the elements of `Fin (k + 1)`. The colouring is a function on all of $\mathbb{N}$, constrained only on $[1, 2m + 1]$, and $x = y$ is allowed in a Schur triple. In `TriangleRamsey k (2 * t + 2)` the colours are natural numbers from any `Finset` of at most $k$ elements, and the pair colouring is a function $\mathbb{N} \to \mathbb{N} \to \mathbb{N}$ that is constrained only on the pairs $x < y$ of the vertex set; for $k \ge 1$ the statement is $R_k(3) \le 2t + 2$. Edge cases: for $t = 0$, $\mathrm{TR}(k, 2)$ holds only for $k = 0$, and then $m = 0$ and both sides are $0$; for $k = 0$ and $t \ge 1$ no Schur colouring of $[1, 2t + 1]$ with one colour exists, since $1 + 1 = 2$. The hypotheses are met for $k = 2$, $t = 2$ ($R_2(3) = 6$, $m = 6$) by the Schur colouring of $[1, 13]$ with classes $\{1, 4, 7, 10, 13\}$, $\{2, 3, 11, 12\}$, $\{5, 6, 8, 9\}$, in which each colour occurs twice in $[1, 6]$.
-- source:
--   A. McKenna, "S(6) ≤ 1801 if R₄(3) ≤ 61: a centred Schur bound and the structure at the frontier", Zenodo (2026), https://doi.org/10.5281/zenodo.23156099, Theorem 4.1 (§4.1, balanced colour classes). Lean source: https://github.com/mysticflounder/schur-centred-bound/blob/v1.0.1/ClassicalSchur/Frontier.lean#L250-L276 (release v1.0.1, doi:10.5281/zenodo.23156444).

import Definitions.Def_ClassicalSchurColoring
import Definitions.Def_ClassicalSchurRamsey
import Mathlib

open ClassicalSchur
open Finset

theorem ClassicalSchur.card_filter_Icc_eq_of_frontier {k t m : ℕ} (hR : TriangleRamsey k (2 * t + 2))
    (hm : m = (k + 1) * t) {c : ℕ → Fin (k + 1)} (hc : SchurColoring (2 * m + 1) c)
    (j : Fin (k + 1)) : ((Icc 1 m).filter fun d => c d = j).card = t := by sorry
