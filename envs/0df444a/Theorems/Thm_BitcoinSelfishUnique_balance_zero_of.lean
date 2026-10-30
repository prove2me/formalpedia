-- Prove2me | Theorems.Thm_BitcoinSelfishUnique_balance_zero_of
-- name    : BitcoinSelfishUnique.balance_zero_of
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T17:09:01.391376+00:00
-- url     : https://prove2.me/theorems/3d9ef063-47c9-45fc-951c-3e80316d4776
-- title:
--   Balance at state 0 for any stationary distribution
-- statement:
--   For any $\alpha, \gamma$ and any $\pi$ with `IsStationary α γ π`: $\pi_0 = (1-\alpha)\pi_0 + \pi_{0'} + (1-\alpha)\pi_2$ (with $\pi_2 = \pi(\text{lead } 1)$). Only invariance is used.
-- source:
--   I. Eyal, E. G. Sirer, Majority is not Enough: Bitcoin Mining is Vulnerable, Financial Cryptography 2014, arXiv:1311.0243, Section 4, equation (7) (the stationary distribution): https://arxiv.org/abs/1311.0243; the selfish-mining mission's BitcoinSelfishMining (State, P, stateSum, stationary)

import Definitions.Def_BitcoinSelfishUnique
import Definitions.Def_BitcoinSelfishMining
open BitcoinSelfishUnique BitcoinSelfishMining

theorem BitcoinSelfishUnique.balance_zero_of (α γ : ℝ) (π : BitcoinSelfishMining.State → ℝ)
    (h : BitcoinSelfishUnique.IsStationary α γ π) :
    π .zero = (1 - α) * π .zero + π .tie + (1 - α) * π (.lead 1) := by sorry
