-- Prove2me | Theorems.Thm_BitcoinSelfishErgodic_cesaro_delta_tendsto
-- name    : BitcoinSelfishErgodic.cesaro_delta_tendsto
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T23:42:25.485638+00:00
-- url     : https://prove2.me/theorems/3de7c97a-83d2-4e81-973b-7a97ef29a4ba
-- title:
--   Cesàro convergence from any state
-- statement:
--   For $0 < \alpha < 1/2$, any $\gamma$ and any start $t$: for every state $s$, `cesaro α γ (delta t) n s → stationary α s`. Tightness gives limit points; each is invariant with mass 1, hence the stationary distribution by the uniqueness mission.
-- source:
--   I. Eyal, E. G. Sirer, Majority is not Enough: Bitcoin Mining is Vulnerable, Financial Cryptography 2014, arXiv:1311.0243, Section 4 (the revenue as a long-run share); the selfish-mining missions BitcoinSelfishMining (chain, revenues, threshold) and BitcoinSelfishUnique (uniqueness of the stationary distribution); standard Markov-chain theory (Cesàro limits, renewal equation)

import Definitions.Def_BitcoinSelfishErgodic
import Definitions.Def_BitcoinSelfishMining
open BitcoinSelfishErgodic BitcoinSelfishMining BitcoinSelfishUnique Filter Topology

theorem BitcoinSelfishErgodic.cesaro_delta_tendsto (α γ : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2)
    (t s : BitcoinSelfishMining.State) :
    Filter.Tendsto (fun n => BitcoinSelfishErgodic.cesaro α γ (BitcoinSelfishErgodic.delta t) n s)
      Filter.atTop (nhds (BitcoinSelfishMining.stationary α s)) := by sorry
