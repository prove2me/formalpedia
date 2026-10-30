-- Prove2me | Theorems.Thm_BitcoinSelfishUnique_balance_tie_of
-- name    : BitcoinSelfishUnique.balance_tie_of
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T17:09:37.484961+00:00
-- url     : https://prove2.me/theorems/5317b22f-96ad-46ad-b654-30999d519efb
-- title:
--   Balance at state 0' for any stationary distribution
-- statement:
--   Under the same hypotheses: $\pi_{0'} = (1-\alpha)\pi_1$.
-- source:
--   I. Eyal, E. G. Sirer, Majority is not Enough: Bitcoin Mining is Vulnerable, Financial Cryptography 2014, arXiv:1311.0243, Section 4, equation (7) (the stationary distribution): https://arxiv.org/abs/1311.0243; the selfish-mining mission's BitcoinSelfishMining (State, P, stateSum, stationary)

import Definitions.Def_BitcoinSelfishUnique
import Definitions.Def_BitcoinSelfishMining
open BitcoinSelfishUnique BitcoinSelfishMining

theorem BitcoinSelfishUnique.balance_tie_of (α γ : ℝ) (π : BitcoinSelfishMining.State → ℝ)
    (h : BitcoinSelfishUnique.IsStationary α γ π) :
    π .tie = (1 - α) * π (.lead 0) := by sorry
