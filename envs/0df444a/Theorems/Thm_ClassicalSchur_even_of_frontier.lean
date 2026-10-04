-- Prove2me | Theorems.Thm_ClassicalSchur_even_of_frontier
-- name    : ClassicalSchur.even_of_frontier
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-10-04T00:30:34.547961+00:00
-- url     : https://prove2.me/theorems/802ac7b8-c017-4de9-bd26-a8d3bd529ff3
-- title:
--   Parity at the frontier: the saturation degree $u$ is even
-- statement:
--   This is the parity condition at the frontier with $k + 2$ colours: the saturation degree $u$ must be even.
--
--   Let $k, u, t, m \in \mathbb{N}$ with $2t = (k+1)u$ and $m = (k+2)t$, and suppose that $\mathrm{TR}(k, u + 1)$ holds, that is, every colouring with at most $k$ colours of the pairs of a finite set of at least $u + 1$ naturals has a monochromatic triangle ($R_k(3) \le u + 1$). Suppose that $c : \mathbb{N} \to \mathrm{Fin}(k+2)$ is a Schur colouring of $[1, 2m + 1]$ with $k + 2$ colours: there are no $x, y \ge 1$ with $x + y \le 2m + 1$ and $c(x) = c(y) = c(x + y)$. Then
--
--   $$
--   u \equiv 0 \pmod 2 .
--   $$
--
--   Read the other way: if $u$ is odd and $\mathrm{TR}(k, u + 1)$, $2t = (k+1)u$, $m = (k+2)t$ hold, then $[1, 2m + 1]$ has no Schur colouring with $k + 2$ colours, so $S(k + 2) \le 2m$, one less than the centred bound. In the case of the goal, $u = 60$ is even, and the parity condition gives no such improvement there.
--
--   **Formalization Note.** The colouring is a function on all of $\mathbb{N}$, and `SchurColoring (2 * m + 1) c` constrains only its values on $[1, 2m+1]$; the case $x = y$ is included, so $c(2x) \ne c(x)$ for $1 \le x \le m$. In `TriangleRamsey k (u + 1)` the colours are natural numbers from any `Finset` of at most $k$ elements, and the pair colouring is a function $\mathbb{N} \to \mathbb{N} \to \mathbb{N}$ that is constrained only on the pairs $x < y$ of the vertex set; for $k \ge 1$ the statement is $R_k(3) \le u + 1$. For $k = 0$ the hypotheses force $u \ge 2$ and $m \ge 2$, and $[1, 2m+1] \supseteq [1, 5]$ has no Schur colouring with two colours, so the statement is vacuous there; the case $k = 1$ is not vacuous. The conclusion is Mathlib's `Even u`. Colours are `Fin (k + 2)`, so there are at least two colours and a colour other than $c(m+1)$ exists. The statement is vacuous for $u = 0$, since $\mathrm{TR}(k, 1)$ is false; the hypotheses are met for $k = 1$, $u = 2$, $t = 2$, $m = 6$ by the Schur colourings of $[1, 13]$ with three colours.
-- source:
--   Note "The frontier of the centred Schur bound: balance, saturation and reflection" (schur-numbers project, 2026-10-02, unpublished), section "Paired endpoint neighbourhoods" (u = |P_i| is even). Lean proof not yet in a public repository.

import Definitions.Def_ClassicalSchurColoring
import Definitions.Def_ClassicalSchurRamsey
import Mathlib

open ClassicalSchur
open Finset

theorem ClassicalSchur.even_of_frontier {k u t m : ℕ} (hR : TriangleRamsey k (u + 1))
    (h2t : 2 * t = (k + 1) * u) (hm : m = (k + 2) * t) {c : ℕ → Fin (k + 2)}
    (hc : SchurColoring (2 * m + 1) c) : Even u := by sorry
