-- Prove2me | Theorems.Thm_CappedBaseStock_base_stock_cost_bound
-- name    : CappedBaseStock.base_stock_cost_bound
-- status  : Proved
-- author  : @StellaXin
-- created : 2026-09-08T01:48:17.401675+00:00
-- url     : https://prove2.me/theorems/072995fb-b5c4-45fb-a18f-ef8017ce0e58
-- title:
--   Proposition 3 — Ordinary base-stock cost bound
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
--   **Claim.** For every feasible pair $(r,z)$, let $S=(L+1)r+2z$. The ordinary base-stock rule at this level satisfies
--
--   $$C(\pi_S)\le2hz+\left[\left(2-\frac1{L+1}\right)p+hL\right](\mu-r).$$
--
--   The base-stock rule is represented exactly by capped base stock with both level and cap equal to $S$. Its cost is the long-run expected average from the empty initial state. In particular, the source's stationary expected-loss inequalities are not presumed to hold at each transient period.
-- source:
--   Linwei Xin, Capped Base-Stock Policies: A 2.33-Approximation, author-supplied LaTeX manuscript (756 lines); public paper listing https://papers.ssrn.com/sol3/papers.cfm?abstract_id=7134538 . Author-supplied source SHA-256: f353793c255e1ebed5f3ec541037284bd926183e3e5b71941f13e79c2d67cb7a. Proposition 3 (`prop-base-stock-bound`), lines 617–622.

import Definitions.Def_CappedBaseStock_Model



open scoped ENNReal

namespace CappedBaseStock


theorem base_stock_cost_bound (P : DemandLaw) (c : Parameters) (r z : ℝ)
    (feasible : CertificateFeasible P c r z) :
    baseStockCost P c (Real.toNNReal (((c.L : ℝ) + 1) * r + 2 * z)) ≤
      ENNReal.ofReal (2 * c.h * z +
        ((2 - 1 / ((c.L : ℝ) + 1)) * c.p + c.h * (c.L : ℝ)) * (mean P - r)) := by sorry

end CappedBaseStock
