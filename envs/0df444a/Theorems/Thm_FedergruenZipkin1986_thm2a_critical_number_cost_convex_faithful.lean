-- Prove2me | Theorems.Thm_FedergruenZipkin1986_thm2a_critical_number_cost_convex_faithful
-- name    : FedergruenZipkin1986.thm2a_critical_number_cost_convex_faithful
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-23T01:02:56.26498+00:00
-- url     : https://prove2.me/theorems/e2e9c44d-0de2-4d91-84e1-0ba3781c1bed
-- title:
--   Theorem 2(a) (p. 204): the average cost $g(\bar y)$ of the critical-number policy is convex with a finite minimizer
-- statement:
--   Consider the capacitated inventory model of §2 under Assumptions 1–4 with $c = 0$: i.i.d. demands $D$ on $\{0,1,\dots\}$ with analytic characteristic function and mean $0 < \mu < b$, $\Pr\{D \le b\} < 1$, production capacity $b$, and a one-period cost $G \ge 0$ that is convex, coercive and of polynomial growth. For an integer $\bar y$ let $\delta[\bar y](x) = \max(x, \min(\bar y, x+b))$ be the critical-number policy and $g(\bar y)$ its long-run average cost,
--   $$g(\bar y) = \lim_{t \to \infty} \frac1t E\Bigl\{\sum_{i=0}^{t-1} G(y_i) \Bigm| x_0 = x,\ \delta[\bar y]\Bigr\},$$
--   which exists and does not depend on the initial state $x$. Then $\bar y \mapsto g(\bar y)$ is convex on $\mathbb{Z}$ and has a finite minimizer $\bar y^*$.
--
--   This is part (a) of Theorem 2 of Federgruen and Zipkin (1986). Together with Theorem 1 it identifies the optimal critical number $y^*$ as a minimizer of $g$ and shows that the same policy $\delta[\bar y^*]$ is optimal for every finite storage capacity $U \ge \bar y^*$.
--
--   **Formalization Note** The average cost is $[0,\infty]$-valued and compared with $g(\bar y)$ through $\mathrm{ENNReal.ofReal}$; nonnegativity of $g$ is stated so that this embedding is faithful. The storage capacity plays no role because $\delta[\bar y]$ never raises inventory above $\max(x_0, \bar y)$.
-- source:
--   Federgruen and Zipkin, An Inventory Model with Limited Production Capacity and Uncertain Demands I. The Average-Cost Criterion, Math. Oper. Res. 11(2) (1986) 193–207, doi:10.1287/moor.11.2.193, p. 204, Theorem 2(a) (with eqs. (10)–(11), pp. 203–204)

import Mathlib
import Definitions.Def_FedergruenZipkin_AvgCost_Model
open FedergruenZipkin.AvgCost
open Filter Topology
open scoped ENNReal

theorem FedergruenZipkin1986.thm2a_critical_number_cost_convex_faithful (M : Model) :
    ∃ gbar : ℤ → ℝ,
      (∀ y, 0 ≤ gbar y) ∧
      (∀ ybar x : ℤ, Tendsto (fun t : ℕ => totalCost M (fun _ => critNum M ybar) t x / (t : ℝ≥0∞))
        atTop (𝓝 (ENNReal.ofReal (gbar ybar)))) ∧
      (∀ y, gbar y - gbar (y - 1) ≤ gbar (y + 1) - gbar y) ∧
      ∃ ystar : ℤ, ∀ y, gbar ystar ≤ gbar y := by sorry
