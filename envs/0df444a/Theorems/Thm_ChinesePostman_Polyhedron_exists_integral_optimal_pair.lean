-- Prove2me | Theorems.Thm_ChinesePostman_Polyhedron_exists_integral_optimal_pair
-- name    : ChinesePostman.Polyhedron.exists_integral_optimal_pair
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T06:39:07.523472+00:00
-- url     : https://prove2.me/theorems/e3c3d4c8-e93d-4f3a-ba55-7bc09e1b43f6
-- title:
--   §3, p. 95 (proved in §4) — for c ≥ 0 there is an integral parity x and a dual y satisfying (3.8), (3.11), (3.12)
-- statement:
--   Let $G$ be a finite graph (parallel edges allowed, no loops) and let $c\in\mathbb R^E$ satisfy $c_e\ge 0$ for every edge. Then there exist
--
--   1. a parity point $x$: $x_e\in\mathbb Z$, $x_e\ge 0$ and $\sum_e a_{ne}x_e\equiv b_n\pmod 2$ for every node $n$ ((3.1), (3.2), (3.6)), and
--   2. a dual vector $(y_S)_{S\text{ odd}}$ with $y_S\ge 0$ (3.7) and $\sum\{y_S: e\text{ meets }S\}\le c_e$ (3.8),
--
--   such that the complementary slackness conditions hold:
--   $$x_e>0\Rightarrow \sum\{y_S : e\text{ meets }S\}=c_e,\qquad y_S>0\Rightarrow \sum\{x_e : e\text{ meets }S\}=1 .$$
--
--   The paper obtains such a pair as the output of the blossom algorithm of §4; together with the previous milestone it shows that the linear program over the postman polyhedron has an integral parity optimum.
--
--   **Formalization Note** The statement is existential, as on the page; the algorithm of §4 is not formalized.
-- source:
--   Edmonds and Johnson, Matching, Euler tours and the Chinese postman, Math. Programming 5 (1973), p. 95, §3 (the algorithm of §4, pp. 96–109)

import Mathlib
import Definitions.Def_ChinesePostman_Polyhedron_Setting

namespace ChinesePostman.Polyhedron

theorem exists_integral_optimal_pair {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : Graph V E) (c : E → ℝ)
    (hc : ∀ e, 0 ≤ c e) :
    ∃ x ∈ parityPoints G, ∃ y : Finset V → ℝ, IsDualFeasible G c y ∧
      (∀ e, 0 < x e → dualLoad G y e = c e) ∧
      (∀ S ∈ oddSets G, 0 < y S → cutSum G x S = 1) := by sorry

end ChinesePostman.Polyhedron
