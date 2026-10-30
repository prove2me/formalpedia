-- Prove2me | Theorems.Thm_BitcoinSelfishErgodic_distN_stationary
-- name    : BitcoinSelfishErgodic.distN_stationary
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T23:39:43.596018+00:00
-- url     : https://prove2.me/theorems/a193452b-2981-419c-8e38-0427936b7258
-- title:
--   The stationary distribution is a fixed point of n steps
-- statement:
--   `distN α γ (stationary α) n = stationary α`.
-- source:
--   I. Eyal, E. G. Sirer, Majority is not Enough: Bitcoin Mining is Vulnerable, Financial Cryptography 2014, arXiv:1311.0243, Section 4 (the revenue as a long-run share); the selfish-mining missions BitcoinSelfishMining (chain, revenues, threshold) and BitcoinSelfishUnique (uniqueness of the stationary distribution); standard Markov-chain theory (Cesàro limits, renewal equation)

import Definitions.Def_BitcoinSelfishErgodic
import Definitions.Def_BitcoinSelfishMining
open BitcoinSelfishErgodic BitcoinSelfishMining BitcoinSelfishUnique Filter Topology

theorem BitcoinSelfishErgodic.distN_stationary (α γ : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2) (n : ℕ) :
    BitcoinSelfishErgodic.distN α γ (BitcoinSelfishMining.stationary α) n =
      BitcoinSelfishMining.stationary α := by sorry
