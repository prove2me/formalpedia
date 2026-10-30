-- Prove2me | Theorems.Thm_BitcoinSelfishErgodic_avgPoolGain_eq
-- name    : BitcoinSelfishErgodic.avgPoolGain_eq
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T23:44:14.333987+00:00
-- url     : https://prove2.me/theorems/4f90be16-6ca6-4327-a18a-62b1504a57a8
-- title:
--   The time-averaged pool gain is the expected gain under the Cesàro average
-- statement:
--   `avgPoolGain α γ n = expPoolGain α γ (cesaro α γ (delta zero) n)`.
-- source:
--   I. Eyal, E. G. Sirer, Majority is not Enough: Bitcoin Mining is Vulnerable, Financial Cryptography 2014, arXiv:1311.0243, Section 4 (the revenue as a long-run share); the selfish-mining missions BitcoinSelfishMining (chain, revenues, threshold) and BitcoinSelfishUnique (uniqueness of the stationary distribution); standard Markov-chain theory (Cesàro limits, renewal equation)

import Definitions.Def_BitcoinSelfishErgodic
open BitcoinSelfishErgodic BitcoinSelfishMining BitcoinSelfishUnique Filter Topology

theorem BitcoinSelfishErgodic.avgPoolGain_eq (α γ : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2) (n : ℕ) :
    BitcoinSelfishErgodic.avgPoolGain α γ n =
      BitcoinSelfishErgodic.expPoolGain α γ
        (BitcoinSelfishErgodic.cesaro α γ (BitcoinSelfishErgodic.delta .zero) n) := by sorry
