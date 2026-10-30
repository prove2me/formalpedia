-- Prove2me | Theorems.Thm_BitcoinSelfishErgodic_avgOthersGain_eq
-- name    : BitcoinSelfishErgodic.avgOthersGain_eq
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T23:44:39.722177+00:00
-- url     : https://prove2.me/theorems/e478a720-c2ba-4cf5-8c37-7caf1ea7f610
-- title:
--   The time-averaged honest gain is the expected gain under the Cesàro average
-- statement:
--   As above for the honest miners.
-- source:
--   I. Eyal, E. G. Sirer, Majority is not Enough: Bitcoin Mining is Vulnerable, Financial Cryptography 2014, arXiv:1311.0243, Section 4 (the revenue as a long-run share); the selfish-mining missions BitcoinSelfishMining (chain, revenues, threshold) and BitcoinSelfishUnique (uniqueness of the stationary distribution); standard Markov-chain theory (Cesàro limits, renewal equation)

import Definitions.Def_BitcoinSelfishErgodic
open BitcoinSelfishErgodic BitcoinSelfishMining BitcoinSelfishUnique Filter Topology

theorem BitcoinSelfishErgodic.avgOthersGain_eq (α γ : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2) (n : ℕ) :
    BitcoinSelfishErgodic.avgOthersGain α γ n =
      BitcoinSelfishErgodic.expOthersGain α γ
        (BitcoinSelfishErgodic.cesaro α γ (BitcoinSelfishErgodic.delta .zero) n) := by sorry
