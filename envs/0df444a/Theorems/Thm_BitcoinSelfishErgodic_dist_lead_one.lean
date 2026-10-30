-- Prove2me | Theorems.Thm_BitcoinSelfishErgodic_dist_lead_one
-- name    : BitcoinSelfishErgodic.dist_lead_one
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T23:36:17.134638+00:00
-- url     : https://prove2.me/theorems/26f565ea-9fa4-4d29-b435-a678df17b05a
-- title:
--   One step into a lead of 2
-- statement:
--   `dist α γ μ (lead 1) = α μ(lead 0) + (1-α) μ(lead 2)`.
-- source:
--   I. Eyal, E. G. Sirer, Majority is not Enough: Bitcoin Mining is Vulnerable, Financial Cryptography 2014, arXiv:1311.0243, Section 4 (the revenue as a long-run share); the selfish-mining missions BitcoinSelfishMining (chain, revenues, threshold) and BitcoinSelfishUnique (uniqueness of the stationary distribution); standard Markov-chain theory (Cesàro limits, renewal equation)

import Definitions.Def_BitcoinSelfishErgodic
import Definitions.Def_BitcoinSelfishMining
open BitcoinSelfishErgodic BitcoinSelfishMining BitcoinSelfishUnique Filter Topology

theorem BitcoinSelfishErgodic.dist_lead_one (α γ : ℝ) (μ : BitcoinSelfishMining.State → ℝ) :
    BitcoinSelfishErgodic.dist α γ μ (.lead 1) = α * μ (.lead 0) + (1 - α) * μ (.lead 2) := by sorry
