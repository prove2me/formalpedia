-- Prove2me | Theorems.Thm_CappedBaseStock_base_stock_cost_of_loss_bound
-- name    : CappedBaseStock.base_stock_cost_of_loss_bound
-- status  : Proved
-- author  : @StellaXin
-- created : 2026-09-08T02:23:13.110003+00:00
-- url     : https://prove2.me/theorems/fbe9993c-6e03-4380-9ea1-9b3c0ccf7f62
-- title:
--   An average lost-sales bound controls ordinary base-stock cost
-- statement:
--   Consider the zero-start lost-sales inventory model with i.i.d. nonnegative demand of finite positive mean $\mu$, lead time $L\ge1$, and holding and lost-sales rates $h,p>0$. Fix any ordinary base-stock level $S\ge0$. Let $\ell_t$ denote lost sales, and let $C(\pi_S)$ be the upper limit of expected average period costs from the empty initial state.
--
--   For every finite real $\ell\ge0$ satisfying
--
--   $$\limsup_{N\to\infty}\frac1N\sum_{t=0}^{N-1}\mathbb E[\ell_t]\le\ell,$$
--
--   the cost satisfies
--
--   $$C(\pi_S)\le\left[h(S-(L+1)\mu)+(p+h(L+1))\ell\right]^+.$$
--
--   This transfers any bound on average lost sales to a total-cost bound at the same stock level. Both averages use the actual zero-start trajectory; no stationary convergence hypothesis is included. The positive-part notation is the exact embedding of the real expression into the model's extended nonnegative cost space.
--
--   **Formalization Note** The real affine expression is formed before applying `ENNReal.ofReal`. Its intercept $h(S-(L+1)\mu)$ can be negative and is not separately truncated.
-- source:
--   Linwei Xin, Capped Base-Stock Policies: A 2.33-Approximation, author-supplied LaTeX manuscript (756 lines), SHA-256 f353793c255e1ebed5f3ec541037284bd926183e3e5b71941f13e79c2d67cb7a. Public paper listing: https://papers.ssrn.com/sol3/papers.cfm?abstract_id=7134538. Proof of Proposition 3 (`prop-base-stock-bound`), lines 627–645, especially the inventory-position and expected-cost identities at lines 628–642; order identity `eq-base-stock-order`, lines 493–496. This helper states the zero-start Cesaro cost-transfer consequence, requiring finite-horizon inventory accounting rather than assuming the source stationary identity at startup.

import Definitions.Def_CappedBaseStock_BaseStockAnalysis

open scoped ENNReal NNReal

namespace CappedBaseStock

theorem base_stock_cost_of_loss_bound (P : DemandLaw) (c : Parameters)
    (S : ℝ≥0) (ell : ℝ) (hell : 0 ≤ ell)
    (hloss : baseStockAverageLoss P c S ≤ ENNReal.ofReal ell) :
    baseStockCost P c S ≤ ENNReal.ofReal
      (c.h * ((S : ℝ) - ((c.L : ℝ) + 1) * mean P) +
        (c.p + c.h * ((c.L : ℝ) + 1)) * ell) := by sorry

end CappedBaseStock
