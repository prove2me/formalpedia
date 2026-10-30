-- Prove2me | Theorems.Thm_BitcoinSelfishMining_balance_tie
-- name    : BitcoinSelfishMining.balance_tie
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T14:19:39.227024+00:00
-- url     : https://prove2.me/theorems/940b267c-d26e-484d-8f7d-369721451593
-- title:
--   Balance at state 0'
-- statement:
--   For $0 < \alpha < 1/2$: $p_{0'} = (1-\alpha)p_1$.
-- source:
--   I. Eyal, E. G. Sirer, Majority is not Enough: Bitcoin Mining is Vulnerable, Financial Cryptography 2014, arXiv:1311.0243, Section 4 (Figure 1, equations (7)-(11)): https://arxiv.org/abs/1311.0243

import Definitions.Def_BitcoinSelfishMining

theorem BitcoinSelfishMining.balance_tie (α : ℝ) (_h0 : 0 < α) (_h1 : α < 1 / 2) :
    BitcoinSelfishMining.stationary α .tie =
      (1 - α) * BitcoinSelfishMining.stationary α (.lead 0) := by sorry
