-- Prove2me | Theorems.Thm_FedergruenZipkin1986_thm1_critical_number_optimal_faithful
-- name    : FedergruenZipkin1986.thm1_critical_number_optimal_faithful
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-23T01:02:59.898531+00:00
-- url     : https://prove2.me/theorems/da49aa0a-30be-4a98-ac84-868e808d1220
-- title:
--   Theorem 1 (p. 202), as stated: convex solution of the optimality equation and strong optimality of the critical-number policy ($0 < U < \infty$)
-- statement:
--   Consider the capacitated periodic-review inventory model of §2: i.i.d. demands $D_t$ on $\{0,1,\dots\}$ with probabilities $p(j)$, analytic characteristic function and mean $0 < \mu < b$, $P(b) = \Pr\{D \le b\} < 1$; production capacity $b$, a positive integer; one-period cost $G \ge 0$, convex, with $G(y) \to \infty$ as $|y| \to \infty$ and $G(y) \le A + B|y|^\rho$; order cost $c = 0$. Let $\bar y^\infty$ be the smallest global minimizer of $G$ and let the inventory capacity $U$ be a finite integer with $U > 0$ and $U \ge \bar y^\infty$. Write $Y(x) = \{y : x \le y \le x+b,\ y \le U\}$.
--
--   1. There exist $g^* \in \mathbb{R}$ and $v^*$ such that $E\,v^*(y - D)$ converges for $y \le U$ and
--   $$g^* + v^*(x) = \min_{y \in Y(x)} \bigl[G(y) + E\,v^*(y-D)\bigr], \qquad x \le U,$$
--   with $v^*$ convex on $\{x \le U\}$ and having a global minimizer $y^*$ with $\bar y^\infty \le y^* \le U$.
--   2. The critical-number policy $\delta^*(x) = \max(x, \min(y^*, x+b))$ has average cost $g^*$ from every initial state $x \le U$, and every feasible Markov policy has, from every initial state $x \le U$, lim-inf average cost at least $g^*$.
--
--   This is Theorem 1 of Federgruen and Zipkin (1986) as printed, with its standing assumption $U > 0$ (p. 195) and without the growth bound $v^* \in V_{\rho+3}$ and the sign $g^* \ge 0$ that the existing theorem FedergruenZipkin.AvgCost.theorem1_critical_number_optimal also asserts.
--
--   **Formalization Note** Expectations are series $\sum_j p(j)\,v(y-j)$; policy costs are $[0,\infty]$-valued. "Strongly optimal" is read from eq. (7), p. 203.
-- source:
--   Federgruen and Zipkin, An Inventory Model with Limited Production Capacity and Uncertain Demands I. The Average-Cost Criterion, Math. Oper. Res. 11(2) (1986) 193–207, doi:10.1287/moor.11.2.193, p. 202, Theorem 1 (standing assumptions §2, pp. 195–196)

import Mathlib
import Definitions.Def_FedergruenZipkin_AvgCost_Model
open FedergruenZipkin.AvgCost

theorem FedergruenZipkin1986.thm1_critical_number_optimal_faithful (M : Model) (U yInf : ℤ)
    (hU0 : 0 < U)
    (hyInf : IsLeast {y : ℤ | ∀ z, M.G y ≤ M.G z} yInf) (hU : yInf ≤ U) :
    ∃ (g : ℝ) (v : ℤ → ℝ) (ystar : ℤ),
      (∀ y ≤ U, Summable (fun j : ℕ => M.p j * v (y - j))) ∧
      OptEq M U g v ∧
      ConvexBelow U v ∧
      ystar ≤ U ∧ yInf ≤ ystar ∧ (∀ x ≤ U, v ystar ≤ v x) ∧
      StronglyOptimal M U (critNum M ystar) g := by sorry
