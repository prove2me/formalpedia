-- Prove2me | Theorems.Thm_BitcoinSelfishErgodic_distN_mix
-- name    : BitcoinSelfishErgodic.distN_mix
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T23:43:26.834384+00:00
-- url     : https://prove2.me/theorems/98b9192d-292c-42c8-a91f-717c8b6a8b25
-- title:
--   n-step distributions are mixtures of point-mass runs
-- statement:
--   For a distribution μ: `distN α γ μ n s = stateSum (fun t => μ t · distN α γ (delta t) n s)`.
-- source:
--   I. Eyal, E. G. Sirer, Majority is not Enough: Bitcoin Mining is Vulnerable, Financial Cryptography 2014, arXiv:1311.0243, Section 4 (the revenue as a long-run share); the selfish-mining missions BitcoinSelfishMining (chain, revenues, threshold) and BitcoinSelfishUnique (uniqueness of the stationary distribution); standard Markov-chain theory (Cesàro limits, renewal equation)

import Definitions.Def_BitcoinSelfishErgodic
import Definitions.Def_BitcoinSelfishMining
open BitcoinSelfishErgodic BitcoinSelfishMining BitcoinSelfishUnique Filter Topology

theorem BitcoinSelfishErgodic.distN_mix (α γ : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2)
    (μ : BitcoinSelfishMining.State → ℝ) (hμ : BitcoinSelfishErgodic.IsDist μ) (n : ℕ)
    (s : BitcoinSelfishMining.State) :
    BitcoinSelfishErgodic.distN α γ μ n s =
      BitcoinSelfishMining.stateSum
        (fun t => μ t * BitcoinSelfishErgodic.distN α γ (BitcoinSelfishErgodic.delta t) n s) := by sorry
