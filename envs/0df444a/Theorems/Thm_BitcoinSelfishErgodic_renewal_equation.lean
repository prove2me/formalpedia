-- Prove2me | Theorems.Thm_BitcoinSelfishErgodic_renewal_equation
-- name    : BitcoinSelfishErgodic.renewal_equation
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T23:47:44.078282+00:00
-- url     : https://prove2.me/theorems/0d902dd7-a191-4d8a-91c7-0952ff510c84
-- title:
--   The renewal equation for returns to zero
-- statement:
--   `returnProb α γ (n+1) = Σ_{k≤n} firstPassage α γ zero k · returnProb α γ (n-k)`.
-- source:
--   I. Eyal, E. G. Sirer, Majority is not Enough: Bitcoin Mining is Vulnerable, Financial Cryptography 2014, arXiv:1311.0243, Section 4 (the revenue as a long-run share); the selfish-mining missions BitcoinSelfishMining (chain, revenues, threshold) and BitcoinSelfishUnique (uniqueness of the stationary distribution); standard Markov-chain theory (Cesàro limits, renewal equation)

import Definitions.Def_BitcoinSelfishErgodic
open BitcoinSelfishErgodic BitcoinSelfishMining BitcoinSelfishUnique Filter Topology

theorem BitcoinSelfishErgodic.renewal_equation (α γ : ℝ) (n : ℕ) :
    BitcoinSelfishErgodic.returnProb α γ (n + 1) =
      ∑ k ∈ Finset.range (n + 1),
        BitcoinSelfishErgodic.firstPassage α γ .zero k * BitcoinSelfishErgodic.returnProb α γ (n - k) := by sorry
