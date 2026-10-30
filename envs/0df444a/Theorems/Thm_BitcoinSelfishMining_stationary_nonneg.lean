-- Prove2me | Theorems.Thm_BitcoinSelfishMining_stationary_nonneg
-- name    : BitcoinSelfishMining.stationary_nonneg
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T14:18:07.151271+00:00
-- url     : https://prove2.me/theorems/c0d5c644-7e34-4d9d-8ac2-9b6f9f2fd5e5
-- title:
--   The stationary probabilities are nonnegative
-- statement:
--   For $0 < \alpha < 1/2$ and every state $s$: `stationary α s` $\ge 0$.
-- source:
--   I. Eyal, E. G. Sirer, Majority is not Enough: Bitcoin Mining is Vulnerable, Financial Cryptography 2014, arXiv:1311.0243, Section 4 (Figure 1, equations (7)-(11)): https://arxiv.org/abs/1311.0243

import Definitions.Def_BitcoinSelfishMining

theorem BitcoinSelfishMining.stationary_nonneg (α : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2)
    (s : BitcoinSelfishMining.State) : 0 ≤ BitcoinSelfishMining.stationary α s := by sorry
