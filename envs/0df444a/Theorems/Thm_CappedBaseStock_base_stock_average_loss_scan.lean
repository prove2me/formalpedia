-- Prove2me | Theorems.Thm_CappedBaseStock_base_stock_average_loss_scan
-- name    : CappedBaseStock.base_stock_average_loss_scan
-- status  : Proved
-- author  : @StellaXin
-- created : 2026-09-08T02:23:04.716533+00:00
-- url     : https://prove2.me/theorems/d7d2bc15-11d1-423b-a95a-f885645d71b2
-- title:
--   Ordinary base-stock average loss is bounded by a demand scan
-- statement:
--   Consider the zero-start lost-sales inventory model with i.i.d. nonnegative demand of finite positive mean, integer lead time $L\ge1$, and positive holding and penalty rates. For any ordinary base-stock level $S\ge0$, let $\ell_t$ be its lost sales and let
--
--   $$V_L=\max_{0\le j\le L}\sum_{i=0}^{L}D_{j+i}.$$
--
--   Then the upper limit of expected average lost sales satisfies
--
--   $$\limsup_{N\to\infty}\frac1N\sum_{t=0}^{N-1}\mathbb E[\ell_t]\le\frac{\mathbb E[(V_L-S)^+]}{L+1}.$$
--
--   The trajectory starts with zero on-hand inventory and an empty pipeline. This is a bound on its long-run average, with no assumption that it starts in stationarity. In particular, the statement does not assert this bound for every individual transient period. It connects the policy dynamics to a demand-only scan and can be reused at any stock level.
-- source:
--   Linwei Xin, Capped Base-Stock Policies: A 2.33-Approximation, author-supplied LaTeX manuscript (756 lines), SHA-256 f353793c255e1ebed5f3ec541037284bd926183e3e5b71941f13e79c2d67cb7a. Public paper listing: https://papers.ssrn.com/sol3/papers.cfm?abstract_id=7134538. Lemma `lem-base-stock-loss`, equations `eq-loss-recursion` and `eq-scan-bound`, lines 536–550 and 556–582, with the greedy-window lemma at lines 502–523. This is the zero-start Cesaro-average counterpart of the stationary scan inequality; finite initial and incomplete blocks must be accounted for, not assumed away.

import Definitions.Def_CappedBaseStock_BaseStockAnalysis

open MeasureTheory
open scoped ENNReal NNReal

namespace CappedBaseStock

theorem base_stock_average_loss_scan (P : DemandLaw) (c : Parameters) (S : ℝ≥0) :
    baseStockAverageLoss P c S ≤
      (∫⁻ d, scanExcess d c.L (S : ℝ) ∂demandPathLaw P) /
        ((c.L : ℝ≥0∞) + 1) := by sorry

end CappedBaseStock
