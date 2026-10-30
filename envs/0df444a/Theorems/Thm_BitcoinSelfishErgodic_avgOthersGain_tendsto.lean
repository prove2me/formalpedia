-- Prove2me | Theorems.Thm_BitcoinSelfishErgodic_avgOthersGain_tendsto
-- name    : BitcoinSelfishErgodic.avgOthersGain_tendsto
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T23:45:44.8259+00:00
-- url     : https://prove2.me/theorems/9c80a3e3-1c26-4f6d-93c4-12cd84c9f29b
-- title:
--   The honest time-averaged revenue converges to the paper's rate
-- statement:
--   `avgOthersGain α γ n → othersRevenue α γ`.
-- source:
--   I. Eyal, E. G. Sirer, Majority is not Enough: Bitcoin Mining is Vulnerable, Financial Cryptography 2014, arXiv:1311.0243, Section 4 (the revenue as a long-run share); the selfish-mining missions BitcoinSelfishMining (chain, revenues, threshold) and BitcoinSelfishUnique (uniqueness of the stationary distribution); standard Markov-chain theory (Cesàro limits, renewal equation)

import Definitions.Def_BitcoinSelfishErgodic
import Definitions.Def_BitcoinSelfishMining
open BitcoinSelfishErgodic BitcoinSelfishMining BitcoinSelfishUnique Filter Topology

theorem BitcoinSelfishErgodic.avgOthersGain_tendsto (α γ : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2) :
    Filter.Tendsto (BitcoinSelfishErgodic.avgOthersGain α γ) Filter.atTop
      (nhds (BitcoinSelfishMining.othersRevenue α γ)) := by sorry
