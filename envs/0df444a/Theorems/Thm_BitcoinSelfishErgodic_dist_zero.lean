-- Prove2me | Theorems.Thm_BitcoinSelfishErgodic_dist_zero
-- name    : BitcoinSelfishErgodic.dist_zero
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T23:28:00.316272+00:00
-- url     : https://prove2.me/theorems/77037334-e76a-4495-9728-5c6c178468b1
-- title:
--   One step into zero
-- statement:
--   `dist α γ μ zero = (1-α)μ(zero) + μ(tie) + (1-α)μ(lead 1)`.
-- source:
--   I. Eyal, E. G. Sirer, Majority is not Enough: Bitcoin Mining is Vulnerable, Financial Cryptography 2014, arXiv:1311.0243, Section 4 (the revenue as a long-run share); the selfish-mining missions BitcoinSelfishMining (chain, revenues, threshold) and BitcoinSelfishUnique (uniqueness of the stationary distribution); standard Markov-chain theory (Cesàro limits, renewal equation)

import Definitions.Def_BitcoinSelfishErgodic
import Definitions.Def_BitcoinSelfishMining
open BitcoinSelfishErgodic BitcoinSelfishMining BitcoinSelfishUnique Filter Topology

theorem BitcoinSelfishErgodic.dist_zero (α γ : ℝ) (μ : BitcoinSelfishMining.State → ℝ) :
    BitcoinSelfishErgodic.dist α γ μ .zero = (1 - α) * μ .zero + μ .tie + (1 - α) * μ (.lead 1) := by sorry
