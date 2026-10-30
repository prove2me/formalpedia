-- Prove2me | Theorems.Thm_BitcoinSelfishErgodic_cesaro_zero_tendsto
-- name    : BitcoinSelfishErgodic.cesaro_zero_tendsto
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T23:42:56.393171+00:00
-- url     : https://prove2.me/theorems/a806168b-136f-4773-9188-6276df4b9b0b
-- title:
--   Cesàro convergence from zero
-- statement:
--   The case $t = \text{zero}$.
-- source:
--   I. Eyal, E. G. Sirer, Majority is not Enough: Bitcoin Mining is Vulnerable, Financial Cryptography 2014, arXiv:1311.0243, Section 4 (the revenue as a long-run share); the selfish-mining missions BitcoinSelfishMining (chain, revenues, threshold) and BitcoinSelfishUnique (uniqueness of the stationary distribution); standard Markov-chain theory (Cesàro limits, renewal equation)

import Definitions.Def_BitcoinSelfishErgodic
import Definitions.Def_BitcoinSelfishMining
open BitcoinSelfishErgodic BitcoinSelfishMining BitcoinSelfishUnique Filter Topology

theorem BitcoinSelfishErgodic.cesaro_zero_tendsto (α γ : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2)
    (s : BitcoinSelfishMining.State) :
    Filter.Tendsto
      (fun n => BitcoinSelfishErgodic.cesaro α γ (BitcoinSelfishErgodic.delta .zero) n s)
      Filter.atTop (nhds (BitcoinSelfishMining.stationary α s)) := by sorry
