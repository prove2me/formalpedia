-- Prove2me | Theorems.Thm_BitcoinSelfishErgodic_avgPoolGain_tendsto
-- name    : BitcoinSelfishErgodic.avgPoolGain_tendsto
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T23:45:18.502246+00:00
-- url     : https://prove2.me/theorems/4d774e3a-57f7-4c06-873f-8263d514eb23
-- title:
--   The pool's time-averaged revenue converges to the paper's rate
-- statement:
--   `avgPoolGain α γ n → poolRevenue α γ`.
-- source:
--   I. Eyal, E. G. Sirer, Majority is not Enough: Bitcoin Mining is Vulnerable, Financial Cryptography 2014, arXiv:1311.0243, Section 4 (the revenue as a long-run share); the selfish-mining missions BitcoinSelfishMining (chain, revenues, threshold) and BitcoinSelfishUnique (uniqueness of the stationary distribution); standard Markov-chain theory (Cesàro limits, renewal equation)

import Definitions.Def_BitcoinSelfishErgodic
import Definitions.Def_BitcoinSelfishMining
open BitcoinSelfishErgodic BitcoinSelfishMining BitcoinSelfishUnique Filter Topology

theorem BitcoinSelfishErgodic.avgPoolGain_tendsto (α γ : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2) :
    Filter.Tendsto (BitcoinSelfishErgodic.avgPoolGain α γ) Filter.atTop
      (nhds (BitcoinSelfishMining.poolRevenue α γ)) := by sorry
