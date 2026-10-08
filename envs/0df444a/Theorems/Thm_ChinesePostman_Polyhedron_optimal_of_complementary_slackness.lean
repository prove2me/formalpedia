-- Prove2me | Theorems.Thm_ChinesePostman_Polyhedron_optimal_of_complementary_slackness
-- name    : ChinesePostman.Polyhedron.optimal_of_complementary_slackness
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T06:38:50.837+00:00
-- url     : https://prove2.me/theorems/793a56c0-00ef-4e0e-aedf-c750d426621f
-- title:
--   §3, (3.11)–(3.12), p. 95 — complementary slackness makes x and y optimal for the primal and dual programs
-- statement:
--   Let $G$ be a finite graph (parallel edges allowed, no loops) and $c\in\mathbb R^E$. Let $x$ lie in the postman polyhedron ((3.2), (3.5)) and let $(y_S)$ be dual feasible ((3.7), (3.8)). Suppose
--   $$x_e>0\ \Longrightarrow\ \sum\{y_S : e\text{ meets }S\}=c_e \tag{3.11}$$
--   for every edge $e$, and
--   $$y_S>0\ \Longrightarrow\ \sum\{x_e : e\text{ meets }S\}=1 \tag{3.12}$$
--   for every odd set $S$. Then
--
--   1. $x$ minimizes $z=\sum_e c_e x_e$ over the postman polyhedron, and
--   2. $y$ maximizes $v=\sum_S y_S$ over all dual feasible vectors.
--
--   These are the optimality conditions that the blossom algorithm of §4 establishes.
-- source:
--   Edmonds and Johnson, Matching, Euler tours and the Chinese postman, Math. Programming 5 (1973), p. 95, §3, (3.11), (3.12)

import Mathlib
import Definitions.Def_ChinesePostman_Polyhedron_Setting

namespace ChinesePostman.Polyhedron

theorem optimal_of_complementary_slackness {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : Graph V E) (c : E → ℝ)
    (x : E → ℝ) (hx : x ∈ postmanPolyhedron G)
    (y : Finset V → ℝ) (hy : IsDualFeasible G c y)
    (h311 : ∀ e, 0 < x e → dualLoad G y e = c e)
    (h312 : ∀ S ∈ oddSets G, 0 < y S → cutSum G x S = 1) :
    (∀ x' ∈ postmanPolyhedron G, objective c x ≤ objective c x') ∧
      (∀ y' : Finset V → ℝ, IsDualFeasible G c y' → dualValue G y' ≤ dualValue G y) := by sorry

end ChinesePostman.Polyhedron
