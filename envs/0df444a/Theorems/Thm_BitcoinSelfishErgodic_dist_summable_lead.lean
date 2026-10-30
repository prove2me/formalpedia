-- Prove2me | Theorems.Thm_BitcoinSelfishErgodic_dist_summable_lead
-- name    : BitcoinSelfishErgodic.dist_summable_lead
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T23:37:27.639796+00:00
-- url     : https://prove2.me/theorems/374cb5dd-3cc5-461f-be46-70e2b6b1e901
-- title:
--   A step preserves lead-summability
-- statement:
--   If μ is summable on the leads, so is `dist α γ μ`.
-- source:
--   I. Eyal, E. G. Sirer, Majority is not Enough: Bitcoin Mining is Vulnerable, Financial Cryptography 2014, arXiv:1311.0243, Section 4 (the revenue as a long-run share); the selfish-mining missions BitcoinSelfishMining (chain, revenues, threshold) and BitcoinSelfishUnique (uniqueness of the stationary distribution); standard Markov-chain theory (Cesàro limits, renewal equation)

import Definitions.Def_BitcoinSelfishErgodic
import Definitions.Def_BitcoinSelfishMining
open BitcoinSelfishErgodic BitcoinSelfishMining BitcoinSelfishUnique Filter Topology

theorem BitcoinSelfishErgodic.dist_summable_lead (α γ : ℝ) (μ : BitcoinSelfishMining.State → ℝ)
    (hμ : Summable (fun n : ℕ => μ (.lead n))) :
    Summable (fun n : ℕ => BitcoinSelfishErgodic.dist α γ μ (.lead n)) := by sorry
