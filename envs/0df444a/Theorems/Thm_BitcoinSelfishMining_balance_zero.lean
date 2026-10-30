-- Prove2me | Theorems.Thm_BitcoinSelfishMining_balance_zero
-- name    : BitcoinSelfishMining.balance_zero
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T14:19:11.846989+00:00
-- url     : https://prove2.me/theorems/8c9dbde7-4978-4e2f-a651-50bda0d8edf6
-- title:
--   Balance at state 0
-- statement:
--   For $0 < \alpha < 1/2$: $p_0 = (1-\alpha)p_0 + p_{0'} + (1-\alpha)p_2$ (with $p_2$ = `stationary α (lead 1)`).
-- source:
--   I. Eyal, E. G. Sirer, Majority is not Enough: Bitcoin Mining is Vulnerable, Financial Cryptography 2014, arXiv:1311.0243, Section 4 (Figure 1, equations (7)-(11)): https://arxiv.org/abs/1311.0243

import Definitions.Def_BitcoinSelfishMining

theorem BitcoinSelfishMining.balance_zero (α : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2) :
    BitcoinSelfishMining.stationary α .zero =
      (1 - α) * BitcoinSelfishMining.stationary α .zero
        + BitcoinSelfishMining.stationary α .tie
        + (1 - α) * BitcoinSelfishMining.stationary α (.lead 1) := by sorry
