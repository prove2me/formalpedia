-- Prove2me | Theorems.Thm_BitcoinSelfishErgodic_dist_nonneg
-- name    : BitcoinSelfishErgodic.dist_nonneg
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T23:37:55.61399+00:00
-- url     : https://prove2.me/theorems/40592ac0-4222-46cb-9780-a382e13e8625
-- title:
--   A step preserves nonnegativity
-- statement:
--   For $0 \le \alpha \le 1$ and nonnegative μ, `dist α γ μ` is nonnegative.
-- source:
--   I. Eyal, E. G. Sirer, Majority is not Enough: Bitcoin Mining is Vulnerable, Financial Cryptography 2014, arXiv:1311.0243, Section 4 (the revenue as a long-run share); the selfish-mining missions BitcoinSelfishMining (chain, revenues, threshold) and BitcoinSelfishUnique (uniqueness of the stationary distribution); standard Markov-chain theory (Cesàro limits, renewal equation)

import Definitions.Def_BitcoinSelfishErgodic
import Definitions.Def_BitcoinSelfishMining
open BitcoinSelfishErgodic BitcoinSelfishMining BitcoinSelfishUnique Filter Topology

theorem BitcoinSelfishErgodic.dist_nonneg (α γ : ℝ) (h0 : 0 ≤ α) (h1 : α ≤ 1)
    (μ : BitcoinSelfishMining.State → ℝ) (hμ : ∀ s, 0 ≤ μ s) (s : BitcoinSelfishMining.State) :
    0 ≤ BitcoinSelfishErgodic.dist α γ μ s := by sorry
