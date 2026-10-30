-- Prove2me | Theorems.Thm_BitcoinSelfishErgodic_dist_stationary
-- name    : BitcoinSelfishErgodic.dist_stationary
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T23:39:19.78327+00:00
-- url     : https://prove2.me/theorems/0ac1a419-6d3b-400a-9bef-fae9ec9a3aad
-- title:
--   The stationary distribution is a fixed point of one step
-- statement:
--   `dist α γ (stationary α) = stationary α` for $0 < \alpha < 1/2$.
-- source:
--   I. Eyal, E. G. Sirer, Majority is not Enough: Bitcoin Mining is Vulnerable, Financial Cryptography 2014, arXiv:1311.0243, Section 4 (the revenue as a long-run share); the selfish-mining missions BitcoinSelfishMining (chain, revenues, threshold) and BitcoinSelfishUnique (uniqueness of the stationary distribution); standard Markov-chain theory (Cesàro limits, renewal equation)

import Definitions.Def_BitcoinSelfishErgodic
import Definitions.Def_BitcoinSelfishMining
open BitcoinSelfishErgodic BitcoinSelfishMining BitcoinSelfishUnique Filter Topology

theorem BitcoinSelfishErgodic.dist_stationary (α γ : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2) :
    BitcoinSelfishErgodic.dist α γ (BitcoinSelfishMining.stationary α) =
      BitcoinSelfishMining.stationary α := by sorry
