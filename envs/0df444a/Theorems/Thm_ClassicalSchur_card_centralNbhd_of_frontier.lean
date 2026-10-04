-- Prove2me | Theorems.Thm_ClassicalSchur_card_centralNbhd_of_frontier
-- name    : ClassicalSchur.card_centralNbhd_of_frontier
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-10-04T00:30:07.684169+00:00
-- url     : https://prove2.me/theorems/894bc33d-e1b8-4169-85ee-0abc8e6f085d
-- title:
--   At the frontier with $k+2$ colours the central neighbourhood $V_m$ has $2t+1$ points
-- statement:
--   This is the size of the central neighbourhood at the frontier with $k + 2$ colours.
--
--   Let $k, u, t, m \in \mathbb{N}$ with
--
--   $$
--   2t = (k+1)u \qquad\text{and}\qquad m = (k+2)t ,
--   $$
--
--   and suppose that $\mathrm{TR}(k, u + 1)$ holds (Lean `TriangleRamsey k (u + 1)`): every colouring with at most $k$ colours of the pairs of a finite set of at least $u + 1$ naturals has a monochromatic triangle, that is, $R_k(3) \le u + 1$. Let $c : \mathbb{N} \to \mathrm{Fin}(k+2)$ be a Schur colouring of $[1, 2m + 1]$ with $k + 2$ colours, and let $V_m$ be the central neighbourhood, the set of neighbours of the centre $m$ of $[0, 2m+1]$ in the colour $c(m+1)$ for the difference colouring $\{x, y\} \mapsto c(|x - y|)$:
--
--   $$
--   V_m = \{\, x \in [0, 2m+1] : x \ne m,\ c(|m - x|) = c(m+1) \,\}.
--   $$
--
--   Then
--
--   $$
--   |V_m| = 2t + 1 .
--   $$
--
--   By the pigeonhole step `ClassicalSchur.triangleRamsey_succ`, the hypothesis gives $R_{k+1}(3) \le 2t + 2$, so $[1, 2m + 1]$ is the frontier interval of the centred bound for $k + 2$ colours. The theorem fixes the size of $V_m$; the saturation theorem then fixes the colour degrees inside it. For six colours under $R_4(3) \le 61$ ($k = 4$, $u = 60$, $t = 150$, $m = 900$) it gives $|V_{900}| = 301$.
--
--   **Formalization Note.** The colouring is a function on all of $\mathbb{N}$, and `SchurColoring (2 * m + 1) c` constrains only its values on $[1, 2m+1]$; the case $x = y$ is included, so $c(2x) \ne c(x)$ for $1 \le x \le m$. In `TriangleRamsey k (u + 1)` the colours are natural numbers from any `Finset` of at most $k$ elements, and the pair colouring is a function $\mathbb{N} \to \mathbb{N} \to \mathbb{N}$ that is constrained only on the pairs $x < y$ of the vertex set; for $k \ge 1$ the statement is $R_k(3) \le u + 1$. For $k = 0$ the hypotheses force $u \ge 2$ and $m \ge 2$, and $[1, 2m+1] \supseteq [1, 5]$ has no Schur colouring with two colours, so the statement is vacuous there; the case $k = 1$ is not vacuous. $V_m$ is the `Finset` `centralNbhd c m`, whose ambient set is `range (2 * m + 2)` $= [0, 2m+1]$, so the point $0$ is a candidate member ($0 \in V_m$ when $c(m) = c(m+1)$); the endpoint $2m + 1$ is always a member. Distances are `Nat.dist`. Edge cases: $\mathrm{TR}(k, 1)$ is false, so $u = 0$ (and hence $t = 0$) makes the statement vacuous. The hypotheses are met for $k = 1$, $u = 2$, $t = 2$, $m = 6$ ($R_1(3) = 3$): for the Schur colouring of $[1, 13]$ with classes $\{1, 4, 7, 10, 13\}$, $\{2, 3, 11, 12\}$, $\{5, 6, 8, 9\}$, the colour $c(7)$ is that of $\{1, 4, 7, 10, 13\}$ and $V_6 = \{2, 5, 7, 10, 13\}$ has $5 = 2t + 1$ points.
-- source:
--   Note "The frontier of the centred Schur bound: balance, saturation and reflection" (schur-numbers project, 2026-10-02, unpublished), section "Nested saturation" (first item: |V| = 2t + 1). Lean proof not yet in a public repository.

import Definitions.Def_ClassicalSchurColoring
import Definitions.Def_ClassicalSchurRamsey
import Mathlib

open ClassicalSchur
open Finset

theorem ClassicalSchur.card_centralNbhd_of_frontier {k u t m : ℕ} (hR : TriangleRamsey k (u + 1))
    (h2t : 2 * t = (k + 1) * u) (hm : m = (k + 2) * t) {c : ℕ → Fin (k + 2)}
    (hc : SchurColoring (2 * m + 1) c) : (centralNbhd c m).card = 2 * t + 1 := by sorry
