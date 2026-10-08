-- Prove2me | Theorems.Thm_ChinesePostman_Polyhedron_min_attained_at_parity_point
-- name    : ChinesePostman.Polyhedron.min_attained_at_parity_point
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T06:39:11.520976+00:00
-- url     : https://prove2.me/theorems/1935b382-bd76-4930-98ef-f67026a4cd63
-- title:
--   §3, (3.19), p. 96 — for c ≥ 0 the minimum of z over the postman polyhedron is attained at a parity point
-- statement:
--   Let $G$ be a finite graph (parallel edges allowed, no loops) and $c\in\mathbb R^E$ with $c_e\ge 0$ for every edge. Then there is a parity point $x$ ($x_e\in\mathbb Z$, $x_e\ge 0$, $\sum_e a_{ne}x_e\equiv b_n \pmod 2$ for every node $n$) such that
--   $$\sum_e c_e x_e\ \le\ \sum_e c_e x'_e\qquad\text{for every } x' \text{ in the postman polyhedron ((3.2), (3.5))}.$$
--
--   So the linear program over the postman polyhedron and the parity problem have the common minimum $z^*$, and the two sets share the supporting hyperplanes $\sum_e c_e x_e\ge z^*$, $c\ge 0$, of (3.19).
--
--   **Formalization Note** The page says "the optimum … will satisfy (3.1) and (3.6)", meaning the optimum produced by the algorithm; since an LP can have non-integral optima as well, the statement is the existence of an optimal parity point.
-- source:
--   Edmonds and Johnson, Matching, Euler tours and the Chinese postman, Math. Programming 5 (1973), p. 96, §3, (3.19)

import Mathlib
import Definitions.Def_ChinesePostman_Polyhedron_Setting

namespace ChinesePostman.Polyhedron

theorem min_attained_at_parity_point {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : Graph V E) (c : E → ℝ)
    (hc : ∀ e, 0 ≤ c e) :
    ∃ x ∈ parityPoints G, ∀ x' ∈ postmanPolyhedron G, objective c x ≤ objective c x' := by sorry

end ChinesePostman.Polyhedron
