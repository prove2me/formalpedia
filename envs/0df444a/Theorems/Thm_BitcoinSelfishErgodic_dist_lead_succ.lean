-- Prove2me | Theorems.Thm_BitcoinSelfishErgodic_dist_lead_succ
-- name    : BitcoinSelfishErgodic.dist_lead_succ
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T23:36:39.241512+00:00
-- url     : https://prove2.me/theorems/7f52504e-478e-4450-a0b7-26fd30c484ac
-- title:
--   One step into a lead of n+3
-- statement:
--   `dist α γ μ (lead (n+2)) = α μ(lead (n+1)) + (1-α) μ(lead (n+3))`.
-- source:
--   I. Eyal, E. G. Sirer, Majority is not Enough: Bitcoin Mining is Vulnerable, Financial Cryptography 2014, arXiv:1311.0243, Section 4 (the revenue as a long-run share); the selfish-mining missions BitcoinSelfishMining (chain, revenues, threshold) and BitcoinSelfishUnique (uniqueness of the stationary distribution); standard Markov-chain theory (Cesàro limits, renewal equation)

import Definitions.Def_BitcoinSelfishErgodic
import Definitions.Def_BitcoinSelfishMining
open BitcoinSelfishErgodic BitcoinSelfishMining BitcoinSelfishUnique Filter Topology

theorem BitcoinSelfishErgodic.dist_lead_succ (α γ : ℝ) (μ : BitcoinSelfishMining.State → ℝ)
    (n : ℕ) :
    BitcoinSelfishErgodic.dist α γ μ (.lead (n + 2)) =
      α * μ (.lead (n + 1)) + (1 - α) * μ (.lead (n + 3)) := by sorry
