-- Prove2me | Theorems.Thm_BitcoinSelfishErgodic_firstReturn_zero
-- name    : BitcoinSelfishErgodic.firstReturn_zero
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T23:46:52.266446+00:00
-- url     : https://prove2.me/theorems/564362ba-87f6-440d-b52c-3c886349fc50
-- title:
--   The first return to zero at time 1 has probability 1−α
-- statement:
--   `firstPassage α γ zero 0 = 1 - α`: the return-time distribution charges time 1, so the renewal sequence is aperiodic.
-- source:
--   I. Eyal, E. G. Sirer, Majority is not Enough: Bitcoin Mining is Vulnerable, Financial Cryptography 2014, arXiv:1311.0243, Section 4 (the revenue as a long-run share); the selfish-mining missions BitcoinSelfishMining (chain, revenues, threshold) and BitcoinSelfishUnique (uniqueness of the stationary distribution); standard Markov-chain theory (Cesàro limits, renewal equation)

import Definitions.Def_BitcoinSelfishErgodic
open BitcoinSelfishErgodic BitcoinSelfishMining BitcoinSelfishUnique Filter Topology

theorem BitcoinSelfishErgodic.firstReturn_zero (α γ : ℝ) :
    BitcoinSelfishErgodic.firstPassage α γ .zero 0 = 1 - α := by sorry
