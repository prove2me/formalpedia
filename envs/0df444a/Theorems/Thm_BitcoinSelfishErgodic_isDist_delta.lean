-- Prove2me | Theorems.Thm_BitcoinSelfishErgodic_isDist_delta
-- name    : BitcoinSelfishErgodic.isDist_delta
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T23:40:04.800684+00:00
-- url     : https://prove2.me/theorems/bc20c1f6-b971-456e-858c-e8f6f359c9ff
-- title:
--   Point masses are distributions
-- statement:
--   `IsDist (delta t)`.
-- source:
--   I. Eyal, E. G. Sirer, Majority is not Enough: Bitcoin Mining is Vulnerable, Financial Cryptography 2014, arXiv:1311.0243, Section 4 (the revenue as a long-run share); the selfish-mining missions BitcoinSelfishMining (chain, revenues, threshold) and BitcoinSelfishUnique (uniqueness of the stationary distribution); standard Markov-chain theory (Cesàro limits, renewal equation)

import Definitions.Def_BitcoinSelfishErgodic
import Definitions.Def_BitcoinSelfishMining
open BitcoinSelfishErgodic BitcoinSelfishMining BitcoinSelfishUnique Filter Topology

theorem BitcoinSelfishErgodic.isDist_delta (t : BitcoinSelfishMining.State) :
    BitcoinSelfishErgodic.IsDist (BitcoinSelfishErgodic.delta t) := by sorry
