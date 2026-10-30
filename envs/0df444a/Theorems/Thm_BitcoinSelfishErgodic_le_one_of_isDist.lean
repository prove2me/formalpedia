-- Prove2me | Theorems.Thm_BitcoinSelfishErgodic_le_one_of_isDist
-- name    : BitcoinSelfishErgodic.le_one_of_isDist
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T23:40:45.008625+00:00
-- url     : https://prove2.me/theorems/1961e316-2adb-499e-9f49-990cd18f1862
-- title:
--   A distribution is at most 1 everywhere
-- statement:
--   `IsDist μ` implies $\mu(s) \le 1$.
-- source:
--   I. Eyal, E. G. Sirer, Majority is not Enough: Bitcoin Mining is Vulnerable, Financial Cryptography 2014, arXiv:1311.0243, Section 4 (the revenue as a long-run share); the selfish-mining missions BitcoinSelfishMining (chain, revenues, threshold) and BitcoinSelfishUnique (uniqueness of the stationary distribution); standard Markov-chain theory (Cesàro limits, renewal equation)

import Definitions.Def_BitcoinSelfishErgodic
import Definitions.Def_BitcoinSelfishMining
open BitcoinSelfishErgodic BitcoinSelfishMining BitcoinSelfishUnique Filter Topology

theorem BitcoinSelfishErgodic.le_one_of_isDist (μ : BitcoinSelfishMining.State → ℝ)
    (hμ : BitcoinSelfishErgodic.IsDist μ) (s : BitcoinSelfishMining.State) : μ s ≤ 1 := by sorry
