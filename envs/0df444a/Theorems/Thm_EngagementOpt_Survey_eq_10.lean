-- Prove2me | Theorems.Thm_EngagementOpt_Survey_eq_10
-- name    : EngagementOpt.Survey.eq_10
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T06:21:15.750435+00:00
-- url     : https://prove2.me/theorems/a5daf98a-7b13-472c-9685-01a7830afa9f
-- title:
--   (10): closed form of $\mathbb E[S\mid T=t]$
-- statement:
--   Let $0<p<1$, $0<q<1$, $\bar v\ge0$, $W>0$, and let $t\ge1$ be an integer. With $\mathbb E[S\mid T=t]=\bar v\,\mathbb E[T_q\mid T=t]-Wt$ as in (8) and (9):
--
--   1. if $p=q$, then
--   $$
--   \mathbb E[S\mid T=t]=\bar v\cdot\frac{t+1}{2}-Wt;
--   $$
--   2. if $p\ne q$, then, with $\beta=q/p$,
--   $$
--   \mathbb E[S\mid T=t]=\bar v\left(\frac{t\beta^t}{\beta^t-1}-\frac{1}{\beta-1}\right)-Wt.
--   $$
--
--   This turns the Bayes ratio (9) into an explicit function of $t$, whose monotonicity Theorem 5.1 analyses.
--
--   **Formalization Note** $\beta^t$ is a natural-number power. In the case $p\ne q$ one has $\beta\ne1$ and hence $\beta^t\ne1$ for $t\ge1$, so no denominator vanishes.
-- source:
--   Kleinberg, Mullainathan, Raghavan, The Challenge of Understanding What Users Want, arXiv:2202.11776v3, pp. 20–21, eq. (10)

import Mathlib
import Definitions.Def_EngagementOpt_Survey_condUtility

namespace EngagementOpt.Survey

/-- arXiv:2202.11776v3, p. 21, (10): for `p, q ∈ (0, 1)`, `v̄ ≥ 0`, `W > 0`, and `t ≥ 1`,
`E[S | T = t] = v̄ (t + 1)/2 - W t` if `p = q`, and
`E[S | T = t] = v̄ (t β^t/(β^t - 1) - 1/(β - 1)) - W t` with `β = q/p` if `p ≠ q`. -/
theorem eq_10 (p q v W : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (hq0 : 0 < q) (hq1 : q < 1)
    (hv : 0 ≤ v) (hW : 0 < W)
    (t : ℕ) (ht : 1 ≤ t) :
    (p = q → condUtility v W p q t = v * (((t : ℝ) + 1) / 2) - W * t) ∧
    (p ≠ q → condUtility v W p q t =
      v * ((t : ℝ) * (q / p) ^ t / ((q / p) ^ t - 1) - 1 / (q / p - 1)) - W * t) := by sorry

end EngagementOpt.Survey
