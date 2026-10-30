-- Prove2me | Theorems.Thm_BitcoinSelfishErgodic_last_exit
-- name    : BitcoinSelfishErgodic.last_exit
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T23:47:17.637636+00:00
-- url     : https://prove2.me/theorems/f42d9075-7c35-427d-97cd-4737437d1dd4
-- title:
--   Last-exit decomposition
-- statement:
--   `distN α γ (delta zero) n s = Σ_{k≤n} returnProb α γ k · taboo α γ zero (n-k) s`.
-- source:
--   I. Eyal, E. G. Sirer, Majority is not Enough: Bitcoin Mining is Vulnerable, Financial Cryptography 2014, arXiv:1311.0243, Section 4 (the revenue as a long-run share); the selfish-mining missions BitcoinSelfishMining (chain, revenues, threshold) and BitcoinSelfishUnique (uniqueness of the stationary distribution); standard Markov-chain theory (Cesàro limits, renewal equation)

import Definitions.Def_BitcoinSelfishErgodic
import Definitions.Def_BitcoinSelfishMining
open BitcoinSelfishErgodic BitcoinSelfishMining BitcoinSelfishUnique Filter Topology

theorem BitcoinSelfishErgodic.last_exit (α γ : ℝ) (n : ℕ) (s : BitcoinSelfishMining.State) :
    BitcoinSelfishErgodic.distN α γ (BitcoinSelfishErgodic.delta .zero) n s =
      ∑ k ∈ Finset.range (n + 1),
        BitcoinSelfishErgodic.returnProb α γ k * BitcoinSelfishErgodic.taboo α γ .zero (n - k) s := by sorry
