-- Prove2me | Theorems.Thm_BitcoinSelfishErgodic_cesaro_tendsto
-- name    : BitcoinSelfishErgodic.cesaro_tendsto
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T23:43:47.896103+00:00
-- url     : https://prove2.me/theorems/2d75ed03-db2e-42ef-9fce-2c397ef91a65
-- title:
--   Cesàro convergence from any initial distribution
-- statement:
--   For any `IsDist μ` and every state $s$: `cesaro α γ μ n s → stationary α s`. The time-averaged occupation of every state converges to the paper's stationary distribution, from any start.
-- source:
--   I. Eyal, E. G. Sirer, Majority is not Enough: Bitcoin Mining is Vulnerable, Financial Cryptography 2014, arXiv:1311.0243, Section 4 (the revenue as a long-run share); the selfish-mining missions BitcoinSelfishMining (chain, revenues, threshold) and BitcoinSelfishUnique (uniqueness of the stationary distribution); standard Markov-chain theory (Cesàro limits, renewal equation)

import Definitions.Def_BitcoinSelfishErgodic
import Definitions.Def_BitcoinSelfishMining
open BitcoinSelfishErgodic BitcoinSelfishMining BitcoinSelfishUnique Filter Topology

theorem BitcoinSelfishErgodic.cesaro_tendsto (α γ : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2)
    (μ : BitcoinSelfishMining.State → ℝ) (hμ : BitcoinSelfishErgodic.IsDist μ)
    (s : BitcoinSelfishMining.State) :
    Filter.Tendsto (fun n => BitcoinSelfishErgodic.cesaro α γ μ n s) Filter.atTop
      (nhds (BitcoinSelfishMining.stationary α s)) := by sorry
