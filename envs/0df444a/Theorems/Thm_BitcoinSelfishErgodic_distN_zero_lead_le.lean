-- Prove2me | Theorems.Thm_BitcoinSelfishErgodic_distN_zero_lead_le
-- name    : BitcoinSelfishErgodic.distN_zero_lead_le
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T23:41:20.619885+00:00
-- url     : https://prove2.me/theorems/ef709d5f-77f7-4b66-9945-fde336c404f3
-- title:
--   Geometric tails from zero
-- statement:
--   From `zero`, the probability of a lead of $m+1$ after any number of steps is at most $(\alpha/(1-\alpha))^m$.
-- source:
--   I. Eyal, E. G. Sirer, Majority is not Enough: Bitcoin Mining is Vulnerable, Financial Cryptography 2014, arXiv:1311.0243, Section 4 (the revenue as a long-run share); the selfish-mining missions BitcoinSelfishMining (chain, revenues, threshold) and BitcoinSelfishUnique (uniqueness of the stationary distribution); standard Markov-chain theory (Cesàro limits, renewal equation)

import Definitions.Def_BitcoinSelfishErgodic
open BitcoinSelfishErgodic BitcoinSelfishMining BitcoinSelfishUnique Filter Topology

theorem BitcoinSelfishErgodic.distN_zero_lead_le (α γ : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2)
    (n m : ℕ) :
    BitcoinSelfishErgodic.distN α γ (BitcoinSelfishErgodic.delta .zero) n (.lead m) ≤
      (α / (1 - α)) ^ m := by sorry
