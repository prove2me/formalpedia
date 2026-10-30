-- Prove2me | Theorems.Thm_BitcoinSelfishMining_relative_revenue
-- name    : BitcoinSelfishMining.relative_revenue
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T14:24:02.282009+00:00
-- url     : https://prove2.me/theorems/3c5af946-b56c-4a07-96f3-afd423543b13
-- title:
--   The relative revenue equals the paper's closed form (10)
-- statement:
--   For $0 < \alpha < 1/2$ and any $\gamma$: `relativeRevenue α γ = closedForm α γ`, i.e. $R = \frac{\alpha(1-\alpha)^2(4\alpha + \gamma(1-2\alpha)) - \alpha^3}{1 - \alpha(1 + (2-\alpha)\alpha)}$.
-- source:
--   I. Eyal, E. G. Sirer, Majority is not Enough: Bitcoin Mining is Vulnerable, Financial Cryptography 2014, arXiv:1311.0243, Section 4 (Figure 1, equations (7)-(11)): https://arxiv.org/abs/1311.0243

import Definitions.Def_BitcoinSelfishMining

theorem BitcoinSelfishMining.relative_revenue (α γ : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2) :
    BitcoinSelfishMining.relativeRevenue α γ = BitcoinSelfishMining.closedForm α γ := by sorry
