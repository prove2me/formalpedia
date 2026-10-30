-- Prove2me | Theorems.Thm_BitcoinSelfishMining_threshold_gamma_one
-- name    : BitcoinSelfishMining.threshold_gamma_one
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T14:25:23.859028+00:00
-- url     : https://prove2.me/theorems/720b0d19-393e-4394-ab9a-ade9e0af71a2
-- title:
--   With every honest miner on the pool's branch, selfish mining always pays
-- statement:
--   For every $0 < \alpha < 1/2$: `relativeRevenue α 1 > α`.
-- source:
--   I. Eyal, E. G. Sirer, Majority is not Enough: Bitcoin Mining is Vulnerable, Financial Cryptography 2014, arXiv:1311.0243, Section 4 (Figure 1, equations (7)-(11)): https://arxiv.org/abs/1311.0243

import Definitions.Def_BitcoinSelfishMining

theorem BitcoinSelfishMining.threshold_gamma_one (α : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2) :
    BitcoinSelfishMining.relativeRevenue α 1 > α := by sorry
