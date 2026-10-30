-- Prove2me | Theorems.Thm_BitcoinSelfishUnique_balance_two_of
-- name    : BitcoinSelfishUnique.balance_two_of
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T17:10:41.082224+00:00
-- url     : https://prove2.me/theorems/7cca7b16-2a9f-44b9-841d-ad6108531db7
-- title:
--   Balance at state 2 for any stationary distribution
-- statement:
--   Under the same hypotheses: $\pi_2 = \alpha\pi_1 + (1-\alpha)\pi_3$.
-- source:
--   I. Eyal, E. G. Sirer, Majority is not Enough: Bitcoin Mining is Vulnerable, Financial Cryptography 2014, arXiv:1311.0243, Section 4, equation (7) (the stationary distribution): https://arxiv.org/abs/1311.0243; the selfish-mining mission's BitcoinSelfishMining (State, P, stateSum, stationary)

import Definitions.Def_BitcoinSelfishUnique
import Definitions.Def_BitcoinSelfishMining
open BitcoinSelfishUnique BitcoinSelfishMining

theorem BitcoinSelfishUnique.balance_two_of (α γ : ℝ) (π : BitcoinSelfishMining.State → ℝ)
    (h : BitcoinSelfishUnique.IsStationary α γ π) :
    π (.lead 1) = α * π (.lead 0) + (1 - α) * π (.lead 2) := by sorry
