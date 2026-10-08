-- Prove2me | Theorems.Thm_BellmanRouting_PolicySpace_policy_space_converges_within_N_sub_one
-- name    : BellmanRouting.PolicySpace.policy_space_converges_within_N_sub_one
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T16:32:55.075603+00:00
-- url     : https://prove2.me/theorems/89682d1c-598e-4d30-b4f9-409e1df4f8f3
-- title:
--   Summary and Section 5 — approximation in policy space reaches the minimal times, the unique solution of (3.2), after at most N − 1 iterations
-- statement:
--   Let $N = n + 1 \ge 2$ cities be given, with travel times $t_{ij} > 0$ for $i \ne j$. Let $f^{(k)}$ be the successive approximations (5.1) started from the direct-route policy (5.2) ($f_i^{(0)} = t_{iN}$ for $i \ne N$, $f_N^{(0)} = 0$). Then for every $k \ge N - 1$:
--   1. for every city $i$, $f_i^{(k)}$ is the minimal time (3.1) to travel from $i$ to $N$: it is the time of some route from $i$ to $N$, and no route from $i$ to $N$ is faster;
--   2. $f^{(k)}$ solves the system (3.2), $f_i^{(k)} = \min_{j\ne i}[t_{ij} + f_j^{(k)}]$ for $i \ne N$ and $f_N^{(k)} = 0$;
--   3. every real solution $F$ of (3.2) equals $f^{(k)}$.
--
--   In the paper's words, the algorithm "converges after at most $(N - 1)$ iterations" (Summary) to the solution of (3.2) (Section 5). In particular, the limit (5.6), $\lim_{k\to\infty} f_i^{(k)} = f_i$, holds and furnishes the solution of (3.2).
--
--   **Formalization Note** "Converges after at most $(N-1)$ iterations" is stated as equality for every $k \ge N - 1$, which is $k \ge n$ with $N = n + 1$. It is not stated as a limit. The bound is the paper's $N - 1$. $f_N^{(0)} = 0$ is the corrected reading of (5.2); see the (5.4) item. The minimal times are defined from routes, not from (3.2) or from the iteration.
-- source:
--   Bellman, On a routing problem, Quart. Appl. Math. 16 (1958), p. 87, Summary; p. 89, Section 5, Eqs. (5.1)–(5.6) and the sentence after (5.6)

import Mathlib
import Definitions.Def_BellmanRouting_PolicySpace_Routing

namespace BellmanRouting.PolicySpace

theorem policy_space_converges_within_N_sub_one {n : ℕ} (hn : 1 ≤ n)
    (t : Fin (n + 1) → Fin (n + 1) → ℝ) (ht : ∀ i j, i ≠ j → 0 < t i j) :
    ∀ k, n ≤ k →
      (∀ i, IsMinTime t i (approx t k i)) ∧
        IsRoutingSolution t (approx t k) ∧
        ∀ F : Fin (n + 1) → ℝ, IsRoutingSolution t F → F = approx t k := by sorry

end BellmanRouting.PolicySpace
