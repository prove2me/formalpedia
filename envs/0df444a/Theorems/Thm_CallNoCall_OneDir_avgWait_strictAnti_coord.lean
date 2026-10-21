-- Prove2me | Theorems.Thm_CallNoCall_OneDir_avgWait_strictAnti_coord
-- name    : CallNoCall.OneDir.avgWait_strictAnti_coord
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T17:27:10.834527+00:00
-- url     : https://prove2.me/theorems/4acc1c40-3319-45f1-80d5-8e1c4f6a7cec
-- title:
--   Proof of Theorem 4, pp. 38–39 — in a state-dependent M/M/k queue with λ > 0 the average waiting time strictly decreases in each service rate µ_m
-- statement:
--   Consider a state-dependent $M/M/k$ queue with arrival rate $\lambda > 0$ and service rates $\mu_n > 0$ ($n \ge 1$) whose average waiting time
--   $$\mathcal W(\mu) = \frac{\sum_{i=1}^{\infty} \frac{i\lambda^{i-1}}{\mu_1\cdots\mu_i}}{1 + \sum_{i=1}^{\infty} \frac{\lambda^{i}}{\mu_1\cdots\mu_i}} - \frac dv$$
--   is finite. Fix a state $m \ge 1$ and two values $0 < x < y$, and let $\mu^{x}$ and $\mu^{y}$ be the rate sequences obtained from $\mu$ by setting the $m$-th rate to $x$, respectively $y$, keeping all other rates. Then both waiting times are finite and
--   $$\mathcal W(\mu^{y}) < \mathcal W(\mu^{x}).$$
--
--   This is the paper's "$\partial\mathcal W/\partial\mu_m < 0$ for any $m$ and $\mu_m$": the average waiting time is strictly decreasing in each single service rate.
--
--   **Formalization Note** The sign of the partial derivative is stated as strict decrease in the single coordinate $\mu_m$, which avoids differentiating an infinite series and is what the sign of the derivative expresses. The hypothesis $\lambda > 0$ is the paper's own: its rewriting $\mathcal W = \frac1\lambda\frac{c_1 + \cdots}{c_2 + \cdots} - v/d$ divides by $\lambda$, and at $\lambda = 0$ the waiting time $1/\mu_1 - d/v$ does not depend on $\mu_m$ for $m \ge 2$. The page prints "$-v/d$" in this display; the mean ride time is $d/v$, as in the waiting-time formula on p. 34, and the constant does not affect the comparison. Finiteness for the two modified sequences is part of the conclusion.
-- source:
--   Feng, Kong, Wang, We Are on the Way: Analysis of On-Demand Ride-Hailing Systems, SSRN working paper 2960991 (version of 2020-04-16), pp. 38–39, Appendix A, proof of Theorem 4

import Mathlib
import Definitions.Def_CallNoCall_OneDir_StateDepQueue

namespace CallNoCall.OneDir

/-- Proof of Theorem 4, pp. 38–39 (`∂W/∂μ_m < 0`): in a state-dependent `M/M/k` queue with
positive rates, arrival rate `λ > 0` and finite average waiting time, raising the single rate
`μ_m` (`m ≥ 1`) from `x > 0` to `y > x`, all other rates fixed, keeps the waiting time finite and
strictly lowers it. -/
theorem avgWait_strictAnti_coord (μ : ℕ → ℝ) (lam d v : ℝ) (hμ : ∀ n, 1 ≤ n → 0 < μ n)
    (hlam : 0 < lam) (hfin : FiniteWait μ lam) (m : ℕ) (hm : 1 ≤ m) (x y : ℝ) (hx : 0 < x)
    (hxy : x < y) :
    FiniteWait (Function.update μ m x) lam ∧ FiniteWait (Function.update μ m y) lam ∧
      avgWait (Function.update μ m y) lam d v < avgWait (Function.update μ m x) lam d v := by sorry

end CallNoCall.OneDir
