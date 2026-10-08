-- Prove2me | Theorems.Thm_ChinesePostman_Polyhedron_odd_set_cut_sum_odd
-- name    : ChinesePostman.Polyhedron.odd_set_cut_sum_odd
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T06:38:29.47975+00:00
-- url     : https://prove2.me/theorems/94979e24-4a6a-4bca-aeef-79e3ef59aff9
-- title:
--   §3, (3.13), p. 95 — parity solutions have an odd sum over the edges meeting an odd set
-- statement:
--   Let $G$ be a finite graph (parallel edges allowed, no loops) with node set $N$ and edge set $E$, let $b_n\in\{0,1\}$ be the parity of the degree of node $n$, and say that an edge meets $S\subseteq N$ when exactly one of its two ends lies in $S$. Let $x\in\mathbb Z^E$ satisfy the parity congruences (3.6)
--   $$\sum_{e\in E} a_{ne}x_e\equiv b_n \pmod 2\qquad (n\in N).$$
--   Then for every odd set $S$ (a set containing an odd number of odd nodes)
--   $$\sum\{x_e : e \text{ meets } S\}\equiv 1 \pmod 2. \tag{3.13}$$
--
--   Combined with $x\ge 0$ this gives the blossom inequality (3.5) for integer parity solutions, the first half of the polyhedral description.
--
--   **Formalization Note** The page also assumes (3.2), $x_e\ge 0$, in this sentence, but the congruence does not use it; the Lean statement omits it, which makes the statement stronger, not weaker.
-- source:
--   Edmonds and Johnson, Matching, Euler tours and the Chinese postman, Math. Programming 5 (1973), p. 95, §3, (3.13)

import Mathlib
import Definitions.Def_ChinesePostman_Polyhedron_Setting

namespace ChinesePostman.Polyhedron

theorem odd_set_cut_sum_odd {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : Graph V E) (z : E → ℤ)
    (hz : ∀ n, incidentSum G z n ≡ bParity G n [ZMOD 2])
    (S : Finset V) (hS : IsOddSet G S) :
    cutSum G z S ≡ 1 [ZMOD 2] := by sorry

end ChinesePostman.Polyhedron
