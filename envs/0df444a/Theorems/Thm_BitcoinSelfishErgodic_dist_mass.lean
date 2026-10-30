-- Prove2me | Theorems.Thm_BitcoinSelfishErgodic_dist_mass
-- name    : BitcoinSelfishErgodic.dist_mass
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T23:37:00.90153+00:00
-- url     : https://prove2.me/theorems/181bd94e-a0da-4f30-b964-124a2fe3b272
-- title:
--   A step preserves total mass
-- statement:
--   For μ summable on the leads, `stateSum (dist α γ μ) = stateSum μ`.
-- source:
--   I. Eyal, E. G. Sirer, Majority is not Enough: Bitcoin Mining is Vulnerable, Financial Cryptography 2014, arXiv:1311.0243, Section 4 (the revenue as a long-run share); the selfish-mining missions BitcoinSelfishMining (chain, revenues, threshold) and BitcoinSelfishUnique (uniqueness of the stationary distribution); standard Markov-chain theory (Cesàro limits, renewal equation)

import Definitions.Def_BitcoinSelfishErgodic
import Definitions.Def_BitcoinSelfishMining
open BitcoinSelfishErgodic BitcoinSelfishMining BitcoinSelfishUnique Filter Topology

theorem BitcoinSelfishErgodic.dist_mass (α γ : ℝ) (μ : BitcoinSelfishMining.State → ℝ)
    (hμ : Summable (fun n : ℕ => μ (.lead n))) :
    BitcoinSelfishMining.stateSum (BitcoinSelfishErgodic.dist α γ μ) =
      BitcoinSelfishMining.stateSum μ := by sorry
