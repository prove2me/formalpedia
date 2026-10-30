-- Prove2me | Theorems.Thm_BitcoinSelfishErgodic_isDist_dist
-- name    : BitcoinSelfishErgodic.isDist_dist
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T23:38:26.575149+00:00
-- url     : https://prove2.me/theorems/362c6f85-4de0-490b-a17c-7825717714eb
-- title:
--   A step maps distributions to distributions
-- statement:
--   For $0 < \alpha < 1/2$, `IsDist μ` implies `IsDist (dist α γ μ)`.
-- source:
--   I. Eyal, E. G. Sirer, Majority is not Enough: Bitcoin Mining is Vulnerable, Financial Cryptography 2014, arXiv:1311.0243, Section 4 (the revenue as a long-run share); the selfish-mining missions BitcoinSelfishMining (chain, revenues, threshold) and BitcoinSelfishUnique (uniqueness of the stationary distribution); standard Markov-chain theory (Cesàro limits, renewal equation)

import Definitions.Def_BitcoinSelfishErgodic
import Definitions.Def_BitcoinSelfishMining
open BitcoinSelfishErgodic BitcoinSelfishMining BitcoinSelfishUnique Filter Topology

theorem BitcoinSelfishErgodic.isDist_dist (α γ : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2)
    (μ : BitcoinSelfishMining.State → ℝ) (hμ : BitcoinSelfishErgodic.IsDist μ) :
    BitcoinSelfishErgodic.IsDist (BitcoinSelfishErgodic.dist α γ μ) := by sorry
