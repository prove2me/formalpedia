-- Prove2me | Theorems.Thm_BitcoinSelfishMining_balance_two
-- name    : BitcoinSelfishMining.balance_two
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T14:20:40.666857+00:00
-- url     : https://prove2.me/theorems/d9f29295-5fce-405d-a3b7-21b634018282
-- title:
--   Balance at state 2
-- statement:
--   For $0 < \alpha < 1/2$: $p_2 = \alpha p_1 + (1-\alpha)p_3$.
-- source:
--   I. Eyal, E. G. Sirer, Majority is not Enough: Bitcoin Mining is Vulnerable, Financial Cryptography 2014, arXiv:1311.0243, Section 4 (Figure 1, equations (7)-(11)): https://arxiv.org/abs/1311.0243

import Definitions.Def_BitcoinSelfishMining

theorem BitcoinSelfishMining.balance_two (α : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2) :
    BitcoinSelfishMining.stationary α (.lead 1) =
      α * BitcoinSelfishMining.stationary α (.lead 0)
        + (1 - α) * BitcoinSelfishMining.stationary α (.lead 2) := by sorry
