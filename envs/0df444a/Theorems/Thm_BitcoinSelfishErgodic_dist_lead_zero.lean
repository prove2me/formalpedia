-- Prove2me | Theorems.Thm_BitcoinSelfishErgodic_dist_lead_zero
-- name    : BitcoinSelfishErgodic.dist_lead_zero
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T23:35:47.977199+00:00
-- url     : https://prove2.me/theorems/05c1b0eb-ff32-496b-ad70-5a0d9e4b20bc
-- title:
--   One step into a lead of 1
-- statement:
--   `dist α γ μ (lead 0) = α μ(zero)`.
-- source:
--   I. Eyal, E. G. Sirer, Majority is not Enough: Bitcoin Mining is Vulnerable, Financial Cryptography 2014, arXiv:1311.0243, Section 4 (the revenue as a long-run share); the selfish-mining missions BitcoinSelfishMining (chain, revenues, threshold) and BitcoinSelfishUnique (uniqueness of the stationary distribution); standard Markov-chain theory (Cesàro limits, renewal equation)

import Definitions.Def_BitcoinSelfishErgodic
import Definitions.Def_BitcoinSelfishMining
open BitcoinSelfishErgodic BitcoinSelfishMining BitcoinSelfishUnique Filter Topology

theorem BitcoinSelfishErgodic.dist_lead_zero (α γ : ℝ) (μ : BitcoinSelfishMining.State → ℝ) :
    BitcoinSelfishErgodic.dist α γ μ (.lead 0) = α * μ .zero := by sorry
