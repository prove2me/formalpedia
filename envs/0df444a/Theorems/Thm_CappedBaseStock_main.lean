-- Prove2me | Theorems.Thm_CappedBaseStock_main
-- name    : CappedBaseStock.main
-- status  : Proved
-- author  : @StellaXin
-- created : 2026-09-08T01:48:52.677812+00:00
-- url     : https://prove2.me/theorems/793e055f-da82-4ed5-b3ab-a34d15280d4b
-- title:
--   Theorem 1 — Exact lead-time bound and the $7/3$ guarantee
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
--   Let $\kappa_L=1+4L^2/((L+1)(3L-1))$. **Claim.**
--
--   $$C^*_{\rm CBS}\le\kappa_L\underline C,$$
--
--   and, as consequences,
--
--   $$C^*_{\rm CBS}\le\kappa_L\mathrm{OPT}\le\frac73\mathrm{OPT}.$$
--
--   These are multiplicative inequalities, including possible zero optimal cost. The statement does not require a minimizing feasible pair or an attained best capped policy. Its only assumptions are the demand-law, positive-cost, and integer-lead-time assumptions of the model; it does not assume the lower bound, either policy comparison, or existence of an optimal stationary realization.
-- source:
--   Linwei Xin, Capped Base-Stock Policies: A 2.33-Approximation, author-supplied LaTeX manuscript (756 lines); public paper listing https://papers.ssrn.com/sol3/papers.cfm?abstract_id=7134538 . Author-supplied source SHA-256: f353793c255e1ebed5f3ec541037284bd926183e3e5b71941f13e79c2d67cb7a. Theorem 1 (`thm-main`), equation `eq-main-bound` and consequences, lines 694–704.

import Definitions.Def_CappedBaseStock_Model



open scoped ENNReal

namespace CappedBaseStock


theorem main (P : DemandLaw) (c : Parameters) :
    CbsOpt P c ≤ ENNReal.ofReal (kappa c.L) * lowerCertificate P c ∧
    CbsOpt P c ≤ ENNReal.ofReal (kappa c.L) * OPT P c ∧
    ENNReal.ofReal (kappa c.L) * OPT P c ≤ (7 / 3 : ℝ≥0∞) * OPT P c := by sorry

end CappedBaseStock
