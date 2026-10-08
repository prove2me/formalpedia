-- Prove2me | Theorems.Thm_BellmanRouting_PolicySpace_approx_succ_le
-- name    : BellmanRouting.PolicySpace.approx_succ_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T16:32:38.255079+00:00
-- url     : https://prove2.me/theorems/f31a3143-6099-4d7b-b150-c6100c1f8e85
-- title:
--   Eq. (5.5) — the approximations in policy space decrease monotonically
-- statement:
--   Let $N = n + 1 \ge 2$ and $t_{ij} > 0$ for $i \ne j$, and let $f^{(k)}$ be defined by (5.1) from the direct-route policy (5.2), with $f_N^{(0)} = 0$. Then
--   $$f_i^{(k+1)} \le f_i^{(k)}, \qquad i = 1, 2, \dots, N, \quad k = 0, 1, 2, \dots$$
--
--   The monotone decrease is the "approximation in policy space" property: each iterate is the value of a policy no worse than the previous one.
--
--   **Formalization Note** $f_N^{(0)} = 0$ is the corrected reading of (5.2); see the (5.4) item. With the printed $f_N^{(0)} = t_{NN} > 0$ the inequality fails already at $k = 0$.
-- source:
--   Bellman, On a routing problem, Quart. Appl. Math. 16 (1958), p. 89, Section 5, Eq. (5.5)

import Mathlib
import Definitions.Def_BellmanRouting_PolicySpace_Routing

namespace BellmanRouting.PolicySpace

theorem approx_succ_le {n : ℕ} (hn : 1 ≤ n)
    (t : Fin (n + 1) → Fin (n + 1) → ℝ) (ht : ∀ i j, i ≠ j → 0 < t i j) :
    ∀ k i, approx t (k + 1) i ≤ approx t k i := by sorry

end BellmanRouting.PolicySpace
