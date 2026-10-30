-- Prove2me | Theorems.Thm_BitcoinSelfishErgodic_distN_delta_lead_le
-- name    : BitcoinSelfishErgodic.distN_delta_lead_le
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T23:41:49.209534+00:00
-- url     : https://prove2.me/theorems/35444cff-7988-4b59-a3b1-c88317962e95
-- title:
--   Uniform geometric tails from any start
-- statement:
--   From any point mass there is $C \ge 1$ with `distN … n (lead m) ≤ C (α/(1-α))^m` for all $n$, $m$: the family of distributions over time is tight.
-- source:
--   I. Eyal, E. G. Sirer, Majority is not Enough: Bitcoin Mining is Vulnerable, Financial Cryptography 2014, arXiv:1311.0243, Section 4 (the revenue as a long-run share); the selfish-mining missions BitcoinSelfishMining (chain, revenues, threshold) and BitcoinSelfishUnique (uniqueness of the stationary distribution); standard Markov-chain theory (Cesàro limits, renewal equation)

import Definitions.Def_BitcoinSelfishErgodic
import Definitions.Def_BitcoinSelfishMining
open BitcoinSelfishErgodic BitcoinSelfishMining BitcoinSelfishUnique Filter Topology

theorem BitcoinSelfishErgodic.distN_delta_lead_le (α γ : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2)
    (t : BitcoinSelfishMining.State) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n m : ℕ,
      BitcoinSelfishErgodic.distN α γ (BitcoinSelfishErgodic.delta t) n (.lead m) ≤
        C * (α / (1 - α)) ^ m := by sorry
