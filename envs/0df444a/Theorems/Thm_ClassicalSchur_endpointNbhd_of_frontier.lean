-- Prove2me | Theorems.Thm_ClassicalSchur_endpointNbhd_of_frontier
-- name    : ClassicalSchur.endpointNbhd_of_frontier
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-10-04T00:30:31.324577+00:00
-- url     : https://prove2.me/theorems/d158a90a-e9f6-4547-8571-8a2a1abd18d0
-- title:
--   Paired endpoint neighbourhoods: $P_i$ has $u$ points, is closed under $x \mapsto 2m - x$ without fixed points, and its differences avoid two colours
-- statement:
--   This describes the endpoint neighbourhoods at the frontier with $k + 2$ colours: each one is a symmetric set of $u$ points whose differences avoid two colours.
--
--   Let $k, u, t, m \in \mathbb{N}$ with $2t = (k+1)u$ and $m = (k+2)t$, and suppose that $\mathrm{TR}(k, u + 1)$ holds, that is, every colouring with at most $k$ colours of the pairs of a finite set of at least $u + 1$ naturals has a monochromatic triangle ($R_k(3) \le u + 1$). Let $c : \mathbb{N} \to \mathrm{Fin}(k+2)$ be a Schur colouring of $[1, 2m + 1]$ with $k + 2$ colours, write $q = c(m+1)$, let $V_m = \{\, x \in [0, 2m+1] : x \ne m,\ c(|m - x|) = q \,\}$ be the central neighbourhood, and for a colour $i$ let
--
--   $$
--   P_i = \{\, x \in V_m : x \ne 2m + 1,\ c(2m + 1 - x) = i \,\}
--   $$
--
--   be the endpoint neighbourhood of colour $i$. If $i \ne q$, then:
--
--   1. $|P_i| = u$;
--   2. for every $x \in P_i$: $2m - x \in P_i$ and $2m - x \ne x$;
--   3. for all $x, y \in P_i$ with $x \ne y$: $c(|x - y|) \ne i$ and $c(|x - y|) \ne q$.
--
--   In short,
--
--   $$
--   |P_i| = u, \qquad 2m - P_i = P_i \ \text{ with no fixed point}, \qquad c(|x - y|) \notin \{i, q\} \ \ (x \ne y \in P_i).
--   $$
--
--   So $P_i$ is the union of $u/2$ pairs $\{m - d, m + d\}$, the reflection $x \mapsto 2m - x$ preserves all differences inside $P_i$, and the difference colouring on $P_i$ uses at most $k$ of the $k + 2$ colours. For six colours under $R_4(3) \le 61$ ($k = 4$, $u = 60$, $m = 900$), each of the five sets $P_i$, $i \ne c(901)$, consists of $30$ pairs $\{900 - d, 900 + d\}$, and its differences use only the four colours other than $i$ and $c(901)$.
--
--   **Formalization Note.** The colouring is a function on all of $\mathbb{N}$, and `SchurColoring (2 * m + 1) c` constrains only its values on $[1, 2m+1]$; the case $x = y$ is included, so $c(2x) \ne c(x)$ for $1 \le x \le m$. In `TriangleRamsey k (u + 1)` the colours are natural numbers from any `Finset` of at most $k$ elements, and the pair colouring is a function $\mathbb{N} \to \mathbb{N} \to \mathbb{N}$ that is constrained only on the pairs $x < y$ of the vertex set; for $k \ge 1$ the statement is $R_k(3) \le u + 1$. For $k = 0$ the hypotheses force $u \ge 2$ and $m \ge 2$, and $[1, 2m+1] \supseteq [1, 5]$ has no Schur colouring with two colours, so the statement is vacuous there; the case $k = 1$ is not vacuous. $P_i$ is the `Finset` `endpointNbhd c m i` $= \Gamma_i(V_m, 2m + 1)$. The subtraction $2m - x$ is truncated, but every $x \in P_i$ satisfies $x \le 2m$ (it lies in $[0, 2m+1]$ and differs from $2m + 1$), so $2m - x$ is the ordinary difference. Distances are `Nat.dist`. The point $0$ can lie in $P_i$, and then $2m$ does too. The statement is vacuous for $u = 0$, since $\mathrm{TR}(k, 1)$ is false. Example ($k = 1$, $u = 2$, $m = 6$): for the Schur colouring of $[1, 13]$ with classes $\{1, 4, 7, 10, 13\}$, $\{2, 3, 11, 12\}$, $\{5, 6, 8, 9\}$, the two endpoint neighbourhoods are $\{2, 10\}$ and $\{5, 7\}$; both are closed under $x \mapsto 12 - x$, and their differences $8$ and $2$ have the colours of $\{5, 6, 8, 9\}$ and $\{2, 3, 11, 12\}$.
-- source:
--   Note "The frontier of the centred Schur bound: balance, saturation and reflection" (schur-numbers project, 2026-10-02, unpublished), section "Paired endpoint neighbourhoods" (|P_i| = u, closure under x ↦ 2m − x without fixed points, differences avoid the colours i and q). Lean proof not yet in a public repository.

import Definitions.Def_ClassicalSchurColoring
import Definitions.Def_ClassicalSchurRamsey
import Mathlib

open ClassicalSchur
open Finset

theorem ClassicalSchur.endpointNbhd_of_frontier {k u t m : ℕ} (hR : TriangleRamsey k (u + 1))
    (h2t : 2 * t = (k + 1) * u) (hm : m = (k + 2) * t) {c : ℕ → Fin (k + 2)}
    (hc : SchurColoring (2 * m + 1) c) {i : Fin (k + 2)} (hi : i ≠ c (m + 1)) :
    (endpointNbhd c m i).card = u ∧
      (∀ x ∈ endpointNbhd c m i, 2 * m - x ∈ endpointNbhd c m i ∧ 2 * m - x ≠ x) ∧
      ∀ x ∈ endpointNbhd c m i, ∀ y ∈ endpointNbhd c m i, x ≠ y →
        c (Nat.dist x y) ≠ i ∧ c (Nat.dist x y) ≠ c (m + 1) := by sorry
