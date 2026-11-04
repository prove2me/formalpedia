-- Prove2me | Theorems.Thm_CappedBaseStock_finite_cap_lost_sales_bound
-- name    : CappedBaseStock.finite_cap_lost_sales_bound
-- status  : Proved
-- author  : @StellaXin
-- created : 2026-09-08T02:18:26.50652+00:00
-- url     : https://prove2.me/theorems/a5d6e9a8-011f-4dbd-9ac5-97b4b5ae35dc
-- title:
--   Finite-cap construction: average lost-sales bound
-- statement:
--   Consider the canonical periodic-review lost-sales model with i.i.d. nonnegative demand of finite positive mean, positive integer lead time, and positive holding and penalty rates. Begin with zero on-hand inventory and an empty pipeline. Fix a feasible certificate pair:
--
--   $$
--   0\le r\le\mu,\qquad z\ge0,\qquad
--   \mathbb E\!\left[\left(I_r^m+\sum_{i=1}^m(D_i-r)-z\right)^+\right]\le m(\mu-r)
--   \quad (m=L,L+1),
--   $$
--
--   where the finite maximum includes the empty sum:
--
--   $$
--   I_r^m=\max_{0\le k\le m}\sum_{i=1}^k(r-D_i).
--   $$
--
--   Run the capped base-stock policy with finite parameters
--
--   $$
--   S=(L+1)r+z,\qquad \text{order cap}=r.
--   $$
--
--   Writing the lost sales in period t as the positive part of demand minus available inventory, the expected Cesàro average obeys
--
--   $$
--   \limsup_{T\to\infty}\frac{1}{T+1}
--   \sum_{t=0}^{T}\mathbb E[\ell_t]
--   \le (\mu-r)+\frac{z+L(\mu-r)}{L+1}.
--   $$
--
--   The upper limit is taken in the extended nonnegative reals. This is a lost-sales-moment bound, with no penalty-cost coefficient. It covers both endpoint caps and zero certificate inventory; no stationary initial law or ergodicity hypothesis is assumed.
--
--   This moment estimate isolates the lost-sales component of Proposition 2 and can be reused with any positive penalty rate. It is the zero-initial-state, long-run formulation of the lost-sales estimate resulting from the manuscript’s finite-cap argument.
-- source:
--   Linwei Xin, Capped Base-Stock Policies: A 2.33-Approximation, author-supplied LaTeX manuscript; public listing https://papers.ssrn.com/sol3/papers.cfm?abstract_id=7134538 . Source SHA-256 f353793c255e1ebed5f3ec541037284bd926183e3e5b71941f13e79c2d67cb7a. Lemma 1 (`lem-cbs-identities`), especially `eq-mean-I-cbs`, lines 337–366, and Proposition 2 (`prop-finite-cap-bound`), `eq-U-upper-envelope`, `eq-U-lower-mean`, `eq-e-mean-bound` with proof, lines 408–488. Derived zero-start Cesàro formulation of the resulting stationary lost-sales moment bound.

import Definitions.Def_CappedBaseStock_Model

open scoped ENNReal

namespace CappedBaseStock

theorem finite_cap_lost_sales_bound (P : DemandLaw) (c : Parameters) (r z : ℝ)
    (feasible : CertificateFeasible P c r z) :
    averageCost P (fun t ω =>
      (lostSales c (cbsRun c (Real.toNNReal (((c.L : ℝ) + 1) * r + z))
        (Real.toNNReal r) ω t) (ω.1 t) : ℝ≥0∞)) ≤
      ENNReal.ofReal ((mean P - r) +
        (z + (c.L : ℝ) * (mean P - r)) / ((c.L : ℝ) + 1)) := by sorry

end CappedBaseStock
