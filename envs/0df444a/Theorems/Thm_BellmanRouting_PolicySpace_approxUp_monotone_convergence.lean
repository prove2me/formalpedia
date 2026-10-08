-- Prove2me | Theorems.Thm_BellmanRouting_PolicySpace_approxUp_monotone_convergence
-- name    : BellmanRouting.PolicySpace.approxUp_monotone_convergence
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T16:32:39.516984+00:00
-- url     : https://prove2.me/theorems/47c4fea2-af6f-41b6-905b-20fcca50a711
-- title:
--   Section 7 — the scheme (7.1) increases, stays below the solution of (3.2) (7.2), and reaches it after finitely many steps
-- statement:
--   Let $N = n + 1 \ge 2$ and $t_{ij} > 0$ for $i \ne j$, and let $f$ be a solution of (3.2). Define the approximations (7.1):
--   $$\underline f_i^{(0)} = \min_{j \ne i} t_{ij}\ (i \ne N),\quad \underline f_N^{(0)} = 0,\qquad \underline f_i^{(k+1)} = \min_{j \ne i}\,[t_{ij} + \underline f_j^{(k)}]\ (i \ne N),\quad \underline f_N^{(k+1)} = 0 .$$
--   Then
--   1. the sequence increases: $\underline f_i^{(k+1)} \ge \underline f_i^{(k)}$ for all $i$ and $k$;
--   2. it is bounded by the solution (7.2): $\underline f_i^{(k)} \le f_i$ for $i = 1, \dots, N$ and $k = 0, 1, 2, \dots$;
--   3. only finitely many iterations are required: there is $K$ such that $\underline f^{(k)} = f$ for every $k \ge K$.
--
--   This is the paper's second scheme, the monotone increasing counterpart of Section 5.
--
--   **Formalization Note** The page writes "converges to $\{f_i\}$ as $k \to \infty$ … only a finite number of iterations will be required". Item 3 states this as eventual equality. The paper gives no bound on $K$, and none is asserted; $K$ may depend on $t$. $f$ is any solution of (3.2), as on the page ("where $\{f_i\}$ is the solution of (3.2)"); such a solution exists and is unique by the (3.2) and Section 4 items. (7.1) prints "$i = 1, 2, \cdots, N = 1$", read as $N - 1$.
-- source:
--   Bellman, On a routing problem, Quart. Appl. Math. 16 (1958), pp. 89–90, Section 7, Eqs. (7.1)–(7.3)

import Mathlib
import Definitions.Def_BellmanRouting_PolicySpace_Routing

namespace BellmanRouting.PolicySpace

theorem approxUp_monotone_convergence {n : ℕ} (hn : 1 ≤ n)
    (t : Fin (n + 1) → Fin (n + 1) → ℝ) (ht : ∀ i j, i ≠ j → 0 < t i j)
    (f : Fin (n + 1) → ℝ) (hf : IsRoutingSolution t f) :
    (∀ k i, approxUp t k i ≤ approxUp t (k + 1) i) ∧
      (∀ k i, approxUp t k i ≤ f i) ∧
      ∃ K : ℕ, ∀ k, K ≤ k → approxUp t k = f := by sorry

end BellmanRouting.PolicySpace
