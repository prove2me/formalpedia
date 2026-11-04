-- Prove2me | Theorems.Thm_CappedBaseStock_finite_cap_inventory_bound
-- name    : CappedBaseStock.finite_cap_inventory_bound
-- status  : Proved
-- author  : @StellaXin
-- created : 2026-09-08T02:18:22.429815+00:00
-- url     : https://prove2.me/theorems/e726955c-b8ee-48cc-b9c5-a94028b22aa5
-- title:
--   Finite-cap construction: average inventory bound
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
--   The expected Cesàro average of post-demand inventory satisfies
--
--   $$
--   \limsup_{T\to\infty}\frac{1}{T+1}
--   \sum_{t=0}^{T}\mathbb E[I_{t+1}]\le z.
--   $$
--
--   The upper limit is taken in the extended nonnegative reals. This is an inventory-moment bound, with no holding-cost coefficient. It requires neither an invariant initial distribution nor convergence to a unique stationary law, and it includes zero cap and zero certificate inventory.
--
--   This moment estimate isolates the inventory component of Proposition 2 and can be reused with any positive holding-cost rate. It is the zero-initial-state, long-run formulation of the inventory estimate in the manuscript’s finite-cap argument.
-- source:
--   Linwei Xin, Capped Base-Stock Policies: A 2.33-Approximation, author-supplied LaTeX manuscript; public listing https://papers.ssrn.com/sol3/papers.cfm?abstract_id=7134538 . Source SHA-256 f353793c255e1ebed5f3ec541037284bd926183e3e5b71941f13e79c2d67cb7a. Finite-cap construction: inventory envelope `eq-I-upper-envelope`, lines 379–402, and its expectation bound in the proof of Proposition 2, lines 459–464. Derived zero-start Cesàro formulation; the source states the corresponding stationary moment argument.

import Definitions.Def_CappedBaseStock_Model

open scoped ENNReal

namespace CappedBaseStock

theorem finite_cap_inventory_bound (P : DemandLaw) (c : Parameters) (r z : ℝ)
    (feasible : CertificateFeasible P c r z) :
    averageCost P (fun t ω =>
      ((cbsRun c (Real.toNNReal (((c.L : ℝ) + 1) * r + z))
        (Real.toNNReal r) ω (t + 1)).1 : ℝ≥0∞)) ≤ ENNReal.ofReal z := by sorry

end CappedBaseStock
