-- Prove2me | Theorems.Thm_ClassicalSchur_card_colorNbhd_centralNbhd_of_frontier
-- name    : ClassicalSchur.card_colorNbhd_centralNbhd_of_frontier
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-10-04T00:30:13.138388+00:00
-- url     : https://prove2.me/theorems/f1ef53ef-b06f-4d7f-b83b-b750260231d0
-- title:
--   Nested saturation: every point of $V_m$ has $u$ neighbours in $V_m$ of each colour other than $c(m+1)$
-- statement:
--   This is the nested saturation of the central neighbourhood: inside $V_m$, every colour other than $c(m+1)$ forms a regular graph of degree $u$.
--
--   Let $k, u, t, m \in \mathbb{N}$ with $2t = (k+1)u$ and $m = (k+2)t$, and suppose that $\mathrm{TR}(k, u + 1)$ holds, that is, every colouring with at most $k$ colours of the pairs of a finite set of at least $u + 1$ naturals has a monochromatic triangle ($R_k(3) \le u + 1$). Let $c : \mathbb{N} \to \mathrm{Fin}(k+2)$ be a Schur colouring of $[1, 2m + 1]$ with $k + 2$ colours, and let $V_m = \{\, x \in [0, 2m+1] : x \ne m,\ c(|m - x|) = c(m+1) \,\}$ be the central neighbourhood. Let $v \in V_m$, and let $i$ be a colour with $i \ne c(m+1)$. Then the colour-$i$ neighbourhood of $v$ inside $V_m$ has $u$ points:
--
--   $$
--   \bigl|\{\, w \in V_m : w \ne v,\ c(|v - w|) = i \,\}\bigr| = u .
--   $$
--
--   So, for the difference colouring restricted to $V_m$, each of the $k + 1$ colours other than $c(m+1)$ is $u$-regular. For six colours under $R_4(3) \le 61$ ($k = 4$, $u = 60$, $t = 150$, $m = 900$), each of the $301$ points of $V_{900}$ has $60$ neighbours in $V_{900}$ of each of the five colours other than $c(901)$. At the endpoint $v = 2m + 1$ the theorem gives the size $u$ of the endpoint neighbourhoods, and at $v = m \pm d$ it supplies the equal colour degrees that force the reflection.
--
--   **Formalization Note.** The colouring is a function on all of $\mathbb{N}$, and `SchurColoring (2 * m + 1) c` constrains only its values on $[1, 2m+1]$; the case $x = y$ is included, so $c(2x) \ne c(x)$ for $1 \le x \le m$. In `TriangleRamsey k (u + 1)` the colours are natural numbers from any `Finset` of at most $k$ elements, and the pair colouring is a function $\mathbb{N} \to \mathbb{N} \to \mathbb{N}$ that is constrained only on the pairs $x < y$ of the vertex set; for $k \ge 1$ the statement is $R_k(3) \le u + 1$. For $k = 0$ the hypotheses force $u \ge 2$ and $m \ge 2$, and $[1, 2m+1] \supseteq [1, 5]$ has no Schur colouring with two colours, so the statement is vacuous there; the case $k = 1$ is not vacuous. The neighbourhood is `colorNbhd c (centralNbhd c m) v i`; it excludes $v$ itself, and distances are `Nat.dist`. The ambient set of $V_m$ is $[0, 2m+1]$, so $0$ may be a member. The colour $i$ ranges over `Fin (k + 2)`. The statement is vacuous for $u = 0$, since $\mathrm{TR}(k, 1)$ is false. Example ($k = 1$, $u = 2$, $t = 2$, $m = 6$): for the Schur colouring of $[1, 13]$ with classes $\{1, 4, 7, 10, 13\}$, $\{2, 3, 11, 12\}$, $\{5, 6, 8, 9\}$ and $V_6 = \{2, 5, 7, 10, 13\}$, the point $13$ has the neighbours $\{2, 10\}$ in the colour of $\{2, 3, 11, 12\}$ and $\{5, 7\}$ in the colour of $\{5, 6, 8, 9\}$.
-- source:
--   Note "The frontier of the centred Schur bound: balance, saturation and reflection" (schur-numbers project, 2026-10-02, unpublished), section "Nested saturation" (second item: each colour degree other than q inside V is u). Lean proof not yet in a public repository.

import Definitions.Def_ClassicalSchurColoring
import Definitions.Def_ClassicalSchurRamsey
import Mathlib

open ClassicalSchur
open Finset

theorem ClassicalSchur.card_colorNbhd_centralNbhd_of_frontier {k u t m : ℕ} (hR : TriangleRamsey k (u + 1))
    (h2t : 2 * t = (k + 1) * u) (hm : m = (k + 2) * t) {c : ℕ → Fin (k + 2)}
    (hc : SchurColoring (2 * m + 1) c) {v : ℕ} (hv : v ∈ centralNbhd c m) {i : Fin (k + 2)}
    (hi : i ≠ c (m + 1)) : (colorNbhd c (centralNbhd c m) v i).card = u := by sorry
