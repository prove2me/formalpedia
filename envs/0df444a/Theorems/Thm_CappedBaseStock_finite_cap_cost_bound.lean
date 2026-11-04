-- Prove2me | Theorems.Thm_CappedBaseStock_finite_cap_cost_bound
-- name    : CappedBaseStock.finite_cap_cost_bound
-- status  : Proved
-- author  : @StellaXin
-- created : 2026-09-08T01:47:47.245283+00:00
-- url     : https://prove2.me/theorems/fa0f3c1f-13c7-4202-9dca-3b5842054ae5
-- title:
--   Proposition 2 — Finite-cap policy cost bound
-- statement:
--   Consider a periodic-review lost-sales inventory system. Demand is i.i.d., nonnegative and real-valued, with $0<\mu=\mathbb E[D]<\infty$. Lead time is an integer $L\ge1$, and holding and lost-sales rates satisfy $h,p>0$. Inventory and the $L$ pipeline coordinates initially equal zero. The first pipeline component arrives, the order is placed before current demand is observed, demand is served up to available inventory, and the remaining pipeline shifts; today's order arrives $L$ periods later. The period cost is $hI_{t+1}+p(D_t-I_t-x_{1,t})^+$.
--
--   Costs use the upper limit of finite-horizon expected average costs from this empty initial state. $\mathrm{OPT}$ is the infimum over all measurable, possibly time-dependent history policies in the canonical demand-path model, with independent uniform private randomization. Infinite expected costs remain infinite. A capped base-stock rule orders $\min\{(S-I_t-\sum_i x_{i,t})^+,r\}$, with finite $S,r\ge0$. Its cost is denoted by $C(\pi_{S,r})$, and $C^*_{\rm CBS}$ is the infimum over these parameters. Ordinary base stock at level $S$ is the same rule with cap $S$.
--
--   For a demand block, let $I_r^m=\max_{0\le k\le m}\sum_{i=1}^k(r-D_i)$, including the zero empty sum. A pair $(r,z)$ is feasible when $0\le r\le\mu$, $z\ge0$, and, for both $m=L$ and $m=L+1$,
--
--   $$\mathbb E\left[\left(I_r^m+\sum_{i=1}^m(D_i-r)-z\right)^+\right]\le m(\mu-r).$$
--
--   The lower certificate $\underline C$ is the infimum of $hz+p(\mu-r)$ over this feasible set. Neither attainment of the infimum nor positivity of $\mathrm{OPT}$ is assumed.
--   **Claim.** For every feasible pair $(r,z)$, choose $S=(L+1)r+z$ and cap $r$. Then
--
--   $$C(\pi_{(L+1)r+z,r})\le\left(h+\frac p{L+1}\right)z+\left(2-\frac1{L+1}\right)p(\mu-r).$$
--
--   This target is the cost conclusion of Proposition 2, equation `eq-finite-cap-bound`. Its other stationary shortfall inequalities are not asserted here. The cost in the conclusion is the original zero-start long-run cost, so any stationary argument used in its proof must be connected to that objective.
-- source:
--   Linwei Xin, Capped Base-Stock Policies: A 2.33-Approximation, author-supplied LaTeX manuscript (756 lines); public paper listing https://papers.ssrn.com/sol3/papers.cfm?abstract_id=7134538 . Author-supplied source SHA-256: f353793c255e1ebed5f3ec541037284bd926183e3e5b71941f13e79c2d67cb7a. Proposition 2 (`prop-finite-cap-bound`), selected cost conclusion `eq-finite-cap-bound`, lines 408–420.

import Definitions.Def_CappedBaseStock_Model



open scoped ENNReal

namespace CappedBaseStock


theorem finite_cap_cost_bound (P : DemandLaw) (c : Parameters) (r z : ℝ)
    (feasible : CertificateFeasible P c r z) :
    cbsCost P c (Real.toNNReal (((c.L : ℝ) + 1) * r + z)) (Real.toNNReal r) ≤
      ENNReal.ofReal ((c.h + c.p / ((c.L : ℝ) + 1)) * z +
        (2 - 1 / ((c.L : ℝ) + 1)) * c.p * (mean P - r)) := by sorry

end CappedBaseStock
