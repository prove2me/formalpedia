-- Prove2me | Theorems.Thm_BitcoinSelfishMining_balance_one
-- name    : BitcoinSelfishMining.balance_one
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T14:20:13.865843+00:00
-- url     : https://prove2.me/theorems/c59fc573-8ac5-4637-82a0-47eb11ccae9f
-- title:
--   Balance at state 1
-- statement:
--   For $0 < \alpha < 1/2$: $p_1 = \alpha p_0$.
-- source:
--   I. Eyal, E. G. Sirer, Majority is not Enough: Bitcoin Mining is Vulnerable, Financial Cryptography 2014, arXiv:1311.0243, Section 4 (Figure 1, equations (7)-(11)): https://arxiv.org/abs/1311.0243

import Definitions.Def_BitcoinSelfishMining

theorem BitcoinSelfishMining.balance_one (α : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2) :
    BitcoinSelfishMining.stationary α (.lead 0) =
      α * BitcoinSelfishMining.stationary α .zero := by sorry
