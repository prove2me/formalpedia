-- Prove2me | Theorems.Thm_BellmanRouting_PolicySpace_approx_eq_minTimeWithin
-- name    : BellmanRouting.PolicySpace.approx_eq_minTimeWithin
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T16:32:28.533563+00:00
-- url     : https://prove2.me/theorems/f2d9fdf9-9ad5-4127-b15b-d2ba64b9f6b3
-- title:
--   Section 5 (after (5.4)) — f_i^(k) is the minimum time over paths with at most k stops
-- statement:
--   Let $N = n + 1 \ge 2$ and $t_{ij} > 0$ for $i \ne j$, and let $f^{(k)}$ be the successive approximations (5.1) from the direct-route policy (5.2), with $f_N^{(0)} = 0$. Then for every $k \ge 0$ and every city $i$, $f_i^{(k)}$ is the minimal time to travel from $i$ to $N$ along a route with at most $k$ stops. That is, some route from $i$ to $N$ with at most $k + 1$ roads has time $f_i^{(k)}$, and every such route has time at least $f_i^{(k)}$:
--   $$f_i^{(k)} = \min\Big\{\sum_{r=0}^{m-1} t_{c_r c_{r+1}} \;:\; i = c_0, c_1, \dots, c_m = N,\ m \le k + 1\Big\}.$$
--
--   The page states this for $k = 1$ ("$f_i^{(1)}$ represents the minimum time for a path with at most one stop"). For general $k$ it invokes the same fact as "the physical interpretation of this iterative scheme", on which both (5.5) and the $N - 1$ bound rest.
--
--   **Formalization Note** At $i = N$ the trivial route (no road, time $0$) is admitted, matching $f_N^{(k)} = 0$. Routes may repeat cities; with positive times this does not change the minimum. The convention $f_N^{(0)} = 0$ is the corrected reading of (5.2) explained in the (5.4) item.
-- source:
--   Bellman, On a routing problem, Quart. Appl. Math. 16 (1958), p. 89, Section 5 (the sentence after (5.4), and the sentence after (5.6))

import Mathlib
import Definitions.Def_BellmanRouting_PolicySpace_Routing

namespace BellmanRouting.PolicySpace

theorem approx_eq_minTimeWithin {n : ℕ} (hn : 1 ≤ n)
    (t : Fin (n + 1) → Fin (n + 1) → ℝ) (ht : ∀ i j, i ≠ j → 0 < t i j) :
    ∀ k i, IsMinTimeWithin t k i (approx t k i) := by sorry

end BellmanRouting.PolicySpace
