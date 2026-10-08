-- Prove2me | Theorems.Thm_BellmanRouting_PolicySpace_routing_equation_unique
-- name    : BellmanRouting.PolicySpace.routing_equation_unique
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T16:32:17.839691+00:00
-- url     : https://prove2.me/theorems/9d110f3f-3dd6-4aa3-a0de-ae7ab63e1a17
-- title:
--   Section 4 — the system (3.2) has at most one solution
-- statement:
--   Let $N = n + 1 \ge 2$ and $t_{ij} > 0$ for all $i \ne j$. If $F$ and $G$ are real vectors indexed by the cities, both solving (3.2), i.e.
--   $$F_i = \min_{j \ne i}\,[t_{ij} + F_j],\quad G_i = \min_{j \ne i}\,[t_{ij} + G_j] \ (i \ne N), \qquad F_N = G_N = 0,$$
--   then $F = G$.
--
--   Together with the existence of the minimal times, this identifies "the solution of (3.2)" with the vector of minimal travel times. Section 7 relies on this identification.
--
--   **Formalization Note** $F$ and $G$ are arbitrary real vectors: no sign or boundedness is assumed. The paper's hypothesis "$t_{ij} > 0$ for all $i, j$" is used only off the diagonal, since the diagonal never enters (3.2).
-- source:
--   Bellman, On a routing problem, Quart. Appl. Math. 16 (1958), p. 88, Section 4, Eqs. (4.1)–(4.6)

import Mathlib
import Definitions.Def_BellmanRouting_PolicySpace_Routing

namespace BellmanRouting.PolicySpace

theorem routing_equation_unique {n : ℕ} (hn : 1 ≤ n)
    (t : Fin (n + 1) → Fin (n + 1) → ℝ) (ht : ∀ i j, i ≠ j → 0 < t i j)
    (F G : Fin (n + 1) → ℝ) (hF : IsRoutingSolution t F) (hG : IsRoutingSolution t G) :
    F = G := by sorry

end BellmanRouting.PolicySpace
