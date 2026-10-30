-- Prove2me | Theorems.Thm_BitcoinSelfishMining_pool_revenue_eq
-- name    : BitcoinSelfishMining.pool_revenue_eq
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T14:23:02.9748+00:00
-- url     : https://prove2.me/theorems/17380c2d-df9e-4ee8-83ef-7b4f75a8a413
-- title:
--   The pool's revenue rate reduces to equation (8)
-- statement:
--   For $0 < \alpha < 1/2$ and any $\gamma$: `poolRevenue α γ` $= p_{0'}(2\alpha + \gamma(1-\alpha)) + p_2 \cdot 2(1-\alpha) + \left(\sum'_{n} p_{\text{lead}(n+2)}\right)(1-\alpha)$, the paper's (8) with the $k \ge 3$ tail as a `tsum`.
-- source:
--   I. Eyal, E. G. Sirer, Majority is not Enough: Bitcoin Mining is Vulnerable, Financial Cryptography 2014, arXiv:1311.0243, Section 4 (Figure 1, equations (7)-(11)): https://arxiv.org/abs/1311.0243

import Definitions.Def_BitcoinSelfishMining

theorem BitcoinSelfishMining.pool_revenue_eq (α γ : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2) :
    BitcoinSelfishMining.poolRevenue α γ =
      BitcoinSelfishMining.stationary α .tie * (α * 2 + γ * (1 - α) * 1)
        + BitcoinSelfishMining.stationary α (.lead 1) * ((1 - α) * 2)
        + (∑' n : ℕ, BitcoinSelfishMining.stationary α (.lead (n + 2))) * ((1 - α) * 1) := by sorry
