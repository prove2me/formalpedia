-- Prove2me | Theorems.Thm_BellmanRouting_PolicySpace_minTimes_satisfy_routing_equation
-- name    : BellmanRouting.PolicySpace.minTimes_satisfy_routing_equation
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T16:31:51.481095+00:00
-- url     : https://prove2.me/theorems/cde2443c-52e6-4829-90b8-94154655eecb
-- title:
--   Eq. (3.2) — the minimal travel times exist and satisfy the routing equation
-- statement:
--   Let $N = n + 1 \ge 2$ cities be given, with travel times $t_{ij} > 0$ for $i \ne j$. Then for every city $i$ the minimal time $f_i$ to travel from $i$ to city $N$ exists (3.1): some route attains it and no route is faster. Moreover, every vector $f$ of minimal times satisfies the nonlinear system (3.2):
--   $$f_i = \min_{j \ne i}\,[t_{ij} + f_j], \quad i = 1, 2, \dots, N-1, \qquad f_N = 0 .$$
--
--   This is the paper's application of the principle of optimality. It connects the route-defined optimal times to the functional equation that the rest of the paper solves.
--
--   **Formalization Note** "Using an optimal policy" in (3.1) becomes an attained minimum over routes (`IsMinTime`), so the existence of an optimal route is part of the conclusion. Routes may repeat cities. With positive times this changes no minimum.
-- source:
--   Bellman, On a routing problem, Quart. Appl. Math. 16 (1958), p. 87, Section 3, Eqs. (3.1)–(3.2)

import Mathlib
import Definitions.Def_BellmanRouting_PolicySpace_Routing

namespace BellmanRouting.PolicySpace

theorem minTimes_satisfy_routing_equation {n : ℕ} (hn : 1 ≤ n)
    (t : Fin (n + 1) → Fin (n + 1) → ℝ) (ht : ∀ i j, i ≠ j → 0 < t i j) :
    (∀ i, ∃ v, IsMinTime t i v) ∧
      ∀ f : Fin (n + 1) → ℝ, (∀ i, IsMinTime t i (f i)) → IsRoutingSolution t f := by sorry

end BellmanRouting.PolicySpace
