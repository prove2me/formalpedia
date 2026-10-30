-- Prove2me | Theorems.Thm_BitcoinSelfishErgodic_dist_tie
-- name    : BitcoinSelfishErgodic.dist_tie
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T23:35:00.814053+00:00
-- url     : https://prove2.me/theorems/cc01c164-d27a-46f2-a7c0-4d03d69a6909
-- title:
--   One step into the tie
-- statement:
--   `dist α γ μ tie = (1-α)μ(lead 0)`.
-- source:
--   I. Eyal, E. G. Sirer, Majority is not Enough: Bitcoin Mining is Vulnerable, Financial Cryptography 2014, arXiv:1311.0243, Section 4 (the revenue as a long-run share); the selfish-mining missions BitcoinSelfishMining (chain, revenues, threshold) and BitcoinSelfishUnique (uniqueness of the stationary distribution); standard Markov-chain theory (Cesàro limits, renewal equation)

import Definitions.Def_BitcoinSelfishErgodic
import Definitions.Def_BitcoinSelfishMining
open BitcoinSelfishErgodic BitcoinSelfishMining BitcoinSelfishUnique Filter Topology

theorem BitcoinSelfishErgodic.dist_tie (α γ : ℝ) (μ : BitcoinSelfishMining.State → ℝ) :
    BitcoinSelfishErgodic.dist α γ μ .tie = (1 - α) * μ (.lead 0) := by sorry
