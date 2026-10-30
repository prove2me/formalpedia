-- Prove2me | Theorems.Thm_BitcoinSelfishMining_others_revenue_eq
-- name    : BitcoinSelfishMining.others_revenue_eq
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T14:23:28.212758+00:00
-- url     : https://prove2.me/theorems/e9f154e0-8887-4302-9b0a-464b146d8415
-- title:
--   The honest revenue rate reduces to equation (9)
-- statement:
--   For all real $\alpha, \gamma$: `othersRevenue α γ` $= p_{0'}(2(1-\alpha)(1-\gamma) + \gamma(1-\alpha)) + p_0 (1-\alpha)$, the paper's (9).
-- source:
--   I. Eyal, E. G. Sirer, Majority is not Enough: Bitcoin Mining is Vulnerable, Financial Cryptography 2014, arXiv:1311.0243, Section 4 (Figure 1, equations (7)-(11)): https://arxiv.org/abs/1311.0243

import Definitions.Def_BitcoinSelfishMining

theorem BitcoinSelfishMining.others_revenue_eq (α γ : ℝ) :
    BitcoinSelfishMining.othersRevenue α γ =
      BitcoinSelfishMining.stationary α .tie * ((1 - α) * (1 - γ) * 2 + γ * (1 - α) * 1)
        + BitcoinSelfishMining.stationary α .zero * ((1 - α) * 1) := by sorry
