-- Prove2me | Theorems.Thm_FedergruenZipkin_AvgCost_theorem1_critical_number_optimal
-- name    : FedergruenZipkin.AvgCost.theorem1_critical_number_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T14:38:28.891021+00:00
-- url     : https://prove2.me/theorems/9acfd5eb-5883-469a-b9f1-1c2a6b7929ed
-- title:
--   Theorem 1 (p. 202) — the optimality equation has a convex solution and a critical-number policy is strongly average-cost optimal
-- statement:
--   Consider the capacitated periodic-review inventory model with i.i.d. integer demands, production capacity $b$, finite storage capacity $U$ and one-period cost $G$ satisfying Assumptions 1–4, with $c = 0$. Let $\bar y^\infty$ be the smallest global minimizer of $G$ and assume $U \ge \bar y^\infty$. The optimality equation is
--   $$g + v(x) = Sv(x) = \min_{y \in Y(x)} \bigl[G(y) + E\,v(y - D)\bigr],\qquad x \le U, \tag{6}$$
--   where $Y(x) = \{y : x \le y \le x + b,\ y \le U\}$.
--
--   **Theorem 1.** (a) There exists a solution $(g^*, v^*)$ of (6) such that $v^*$ is convex and has a finite global minimizer $y^* \ge \bar y^\infty$.
--   (b) The critical-number policy $\delta^*$ with critical number $y^*$,
--   $$\delta^*(x) = \max\bigl(x, \min(y^*, x + b)\bigr),$$
--   is strongly optimal, and its average cost is $g^*$: from every initial state $x \le U$,
--   $$\lim_{t\to\infty} t^{-1} E\Bigl\{\sum_{i=0}^{t-1} G(y_i) \Bigm| x_0 = x, \delta^*\Bigr\} = g^*,$$
--   and every Markov policy $\pi$ satisfies, from every initial state $x \le U$,
--   $$\liminf_{t\to\infty} t^{-1} E\Bigl\{\sum_{i=0}^{t-1} G(y_i) \Bigm| x_0 = x, \pi\Bigr\} \ge g^*.$$
--
--   Under a finite storage capacity, a modified base-stock policy — order up to $y^*$, but never more than the capacity $b$ — is optimal under the average-cost criterion in the strong sense, against all memoryless policies and from every starting state.
--
--   **Formalization Note** The statement asserts the existence of $g$, $v$ and $y^*$ jointly, so the $y^*$ of (b) is the minimizer produced in (a). Besides the printed conclusions it records: the convergence of $E\,v(y-D)$ for $y \le U$ (so that (6) is not satisfied through a divergent series), $|v(x)| \le A + B|x|^{\rho+3}$ (the proof constructs $v^* \in V \subset V_{\rho+3}$), and $g \ge 0$ (an average of nonnegative costs). Convexity and global minimality of $v^*$ refer to the states $x \le U$. "Strongly optimal" is read from the proof of (b), eq. (7) on p. 203, which compares with every Markov (memoryless, possibly nonstationary) policy from every initial state. Policy costs are $[0,\infty]$-valued. The order cost is zero ($c = 0$, p. 195), and $U \ge \bar y^\infty$ is the paper's standing convention (p. 195).
-- source:
--   Federgruen and Zipkin, An Inventory Model with Limited Production Capacity and Uncertain Demands I, Math. Oper. Res. 11(2), 1986, p. 202, Theorem 1 (with eq. (6), p. 202, and eq. (7), p. 203)

import Mathlib
import Definitions.Def_FedergruenZipkin_AvgCost_Model

namespace FedergruenZipkin.AvgCost
theorem theorem1_critical_number_optimal (M : Model) (U yInf : ℤ)
    (hyInf : IsLeast {y : ℤ | ∀ z, M.G y ≤ M.G z} yInf) (hU : yInf ≤ U) :
    ∃ (g : ℝ) (v : ℤ → ℝ) (ystar : ℤ),
      (∀ y ≤ U, Summable (fun j : ℕ => M.p j * v (y - j))) ∧
      (∃ A B : ℝ, ∀ x ≤ U, |v x| ≤ A + B * |(x : ℝ)| ^ (M.ρ + 3)) ∧
      0 ≤ g ∧
      OptEq M U g v ∧
      ConvexBelow U v ∧
      ystar ≤ U ∧ yInf ≤ ystar ∧ (∀ x ≤ U, v ystar ≤ v x) ∧
      StronglyOptimal M U (critNum M ystar) g := by sorry
end FedergruenZipkin.AvgCost
