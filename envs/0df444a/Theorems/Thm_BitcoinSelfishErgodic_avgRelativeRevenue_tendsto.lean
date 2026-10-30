-- Prove2me | Theorems.Thm_BitcoinSelfishErgodic_avgRelativeRevenue_tendsto
-- name    : BitcoinSelfishErgodic.avgRelativeRevenue_tendsto
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T23:46:06.55438+00:00
-- url     : https://prove2.me/theorems/447dcb6c-9f80-4636-a44f-f1068d88d124
-- title:
--   The pool's long-run revenue share is the paper's relative revenue
-- statement:
--   For $0 < \alpha < 1/2$ and $0 \le \gamma \le 1$: `avgRelativeRevenue α γ n → relativeRevenue α γ`. Eyal and Sirer's formula is the long-run share of a pool that starts with no lead, not only a stationary quantity.
-- source:
--   I. Eyal, E. G. Sirer, Majority is not Enough: Bitcoin Mining is Vulnerable, Financial Cryptography 2014, arXiv:1311.0243, Section 4 (the revenue as a long-run share); the selfish-mining missions BitcoinSelfishMining (chain, revenues, threshold) and BitcoinSelfishUnique (uniqueness of the stationary distribution); standard Markov-chain theory (Cesàro limits, renewal equation)

import Definitions.Def_BitcoinSelfishErgodic
import Definitions.Def_BitcoinSelfishMining
open BitcoinSelfishErgodic BitcoinSelfishMining BitcoinSelfishUnique Filter Topology

theorem BitcoinSelfishErgodic.avgRelativeRevenue_tendsto (α γ : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2)
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    Filter.Tendsto (BitcoinSelfishErgodic.avgRelativeRevenue α γ) Filter.atTop
      (nhds (BitcoinSelfishMining.relativeRevenue α γ)) := by sorry
