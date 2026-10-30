-- Prove2me | Theorems.Thm_BitcoinSelfishErgodic_isDist_distN
-- name    : BitcoinSelfishErgodic.isDist_distN
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T23:38:52.302021+00:00
-- url     : https://prove2.me/theorems/c605978c-e8e6-4eaa-9e07-5ebd5f9968e5
-- title:
--   n steps map distributions to distributions
-- statement:
--   `IsDist μ` implies `IsDist (distN α γ μ n)` for every $n$.
-- source:
--   I. Eyal, E. G. Sirer, Majority is not Enough: Bitcoin Mining is Vulnerable, Financial Cryptography 2014, arXiv:1311.0243, Section 4 (the revenue as a long-run share); the selfish-mining missions BitcoinSelfishMining (chain, revenues, threshold) and BitcoinSelfishUnique (uniqueness of the stationary distribution); standard Markov-chain theory (Cesàro limits, renewal equation)

import Definitions.Def_BitcoinSelfishErgodic
import Definitions.Def_BitcoinSelfishMining
open BitcoinSelfishErgodic BitcoinSelfishMining BitcoinSelfishUnique Filter Topology

theorem BitcoinSelfishErgodic.isDist_distN (α γ : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2)
    (μ : BitcoinSelfishMining.State → ℝ) (hμ : BitcoinSelfishErgodic.IsDist μ) (n : ℕ) :
    BitcoinSelfishErgodic.IsDist (BitcoinSelfishErgodic.distN α γ μ n) := by sorry
