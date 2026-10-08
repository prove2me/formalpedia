-- Prove2me | Theorems.Thm_BellmanRouting_PolicySpace_approx_one_le_approx_zero
-- name    : BellmanRouting.PolicySpace.approx_one_le_approx_zero
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T16:32:16.192979+00:00
-- url     : https://prove2.me/theorems/3a2b02f5-5bac-4bd3-b085-18f73d9b7bdb
-- title:
--   Eq. (5.4) — the first approximation from the direct-route policy does not exceed it
-- statement:
--   Let $N = n + 1 \ge 2$ and $t_{ij} > 0$ for $i \ne j$. Let $f^{(0)}$ be the direct-route policy (5.2), $f_i^{(0)} = t_{iN}$ for $i \ne N$ and $f_N^{(0)} = 0$, and let $f^{(1)}$ be given by (5.3): $f_i^{(1)} = \min_{j \ne i}[t_{ij} + f_j^{(0)}]$ for $i \ne N$, $f_N^{(1)} = 0$. Then
--   $$f_i^{(1)} \le f_i^{(0)}, \qquad i = 1, 2, \dots, N .$$
--
--   This is the first step of the monotone decrease (5.5).
--
--   **Formalization Note** The paper prints (5.2) for $i = 1, \dots, N$, which gives $f_N^{(0)} = t_{NN}$. Read literally, (5.4) is then false whenever $t_{NN} > 0$. For $N = 2$: $f_1^{(1)} = t_{12} + f_2^{(0)} = t_{12} + t_{22} > t_{12} = f_1^{(0)}$. The paper's own justification ("$f_i^{(1)}$ represents the minimum time for a path with at most one stop") requires $f_N^{(0)} = 0$, which is what is used here. This is equivalent to the printed (5.2) under $t_{NN} = 0$.
-- source:
--   Bellman, On a routing problem, Quart. Appl. Math. 16 (1958), p. 89, Section 5, Eqs. (5.2)–(5.4)

import Mathlib
import Definitions.Def_BellmanRouting_PolicySpace_Routing

namespace BellmanRouting.PolicySpace

theorem approx_one_le_approx_zero {n : ℕ} (hn : 1 ≤ n)
    (t : Fin (n + 1) → Fin (n + 1) → ℝ) (ht : ∀ i j, i ≠ j → 0 < t i j) :
    ∀ i, approx t 1 i ≤ approx t 0 i := by sorry

end BellmanRouting.PolicySpace
