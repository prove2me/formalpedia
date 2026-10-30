-- Prove2me | Theorems.Thm_BitcoinSelfishUnique_balance_one_of
-- name    : BitcoinSelfishUnique.balance_one_of
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T17:10:03.626327+00:00
-- url     : https://prove2.me/theorems/63884cd7-1f2e-4e98-a9c3-607a78a343e5
-- title:
--   Balance at state 1 for any stationary distribution
-- statement:
--   Under the same hypotheses: $\pi_1 = \alpha\pi_0$.
-- source:
--   I. Eyal, E. G. Sirer, Majority is not Enough: Bitcoin Mining is Vulnerable, Financial Cryptography 2014, arXiv:1311.0243, Section 4, equation (7) (the stationary distribution): https://arxiv.org/abs/1311.0243; the selfish-mining mission's BitcoinSelfishMining (State, P, stateSum, stationary)

import Definitions.Def_BitcoinSelfishUnique
import Definitions.Def_BitcoinSelfishMining
open BitcoinSelfishUnique BitcoinSelfishMining

theorem BitcoinSelfishUnique.balance_one_of (α γ : ℝ) (π : BitcoinSelfishMining.State → ℝ)
    (h : BitcoinSelfishUnique.IsStationary α γ π) :
    π (.lead 0) = α * π .zero := by sorry
