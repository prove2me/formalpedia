-- Prove2me | Theorems.Thm_BitcoinSelfishErgodic_avgRelativeRevenue_eventually_gt
-- name    : BitcoinSelfishErgodic.avgRelativeRevenue_eventually_gt
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T23:46:27.912099+00:00
-- url     : https://prove2.me/theorems/dfa5c1c4-a2c9-4b6f-9148-9a66e656958c
-- title:
--   Above the threshold, the pool's realized share eventually exceeds its hashrate
-- statement:
--   For $0 < \alpha < 1/2$, $0 \le \gamma \le 1$ and $\alpha > (1-\gamma)/(3-2\gamma)$: for all large $n$, $\alpha <$ `avgRelativeRevenue α γ n`. The threshold theorem as a statement about time.
-- source:
--   I. Eyal, E. G. Sirer, Majority is not Enough: Bitcoin Mining is Vulnerable, Financial Cryptography 2014, arXiv:1311.0243, Section 4 (the revenue as a long-run share); the selfish-mining missions BitcoinSelfishMining (chain, revenues, threshold) and BitcoinSelfishUnique (uniqueness of the stationary distribution); standard Markov-chain theory (Cesàro limits, renewal equation)

import Definitions.Def_BitcoinSelfishErgodic
import Definitions.Def_BitcoinSelfishMining
open BitcoinSelfishErgodic BitcoinSelfishMining BitcoinSelfishUnique Filter Topology

theorem BitcoinSelfishErgodic.avgRelativeRevenue_eventually_gt (α γ : ℝ) (h0 : 0 < α)
    (h1 : α < 1 / 2) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hT : α > BitcoinSelfishMining.profitThreshold γ) :
    ∀ᶠ n in Filter.atTop, α < BitcoinSelfishErgodic.avgRelativeRevenue α γ n := by sorry
