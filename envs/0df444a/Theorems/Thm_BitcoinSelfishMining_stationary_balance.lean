-- Prove2me | Theorems.Thm_BitcoinSelfishMining_stationary_balance
-- name    : BitcoinSelfishMining.stationary_balance
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T14:21:49.352985+00:00
-- url     : https://prove2.me/theorems/422bef84-5888-402b-88ec-f44e70e8e7bc
-- title:
--   The paper's distribution is invariant for the chain
-- statement:
--   For $0 < \alpha < 1/2$, any $\gamma$ and every state $s$: `stationary α s = stateSum (fun t => stationary α t * P α γ t s)`. The balance equations are derived from `step` and `outcomeProb`, not postulated.
-- source:
--   I. Eyal, E. G. Sirer, Majority is not Enough: Bitcoin Mining is Vulnerable, Financial Cryptography 2014, arXiv:1311.0243, Section 4 (Figure 1, equations (7)-(11)): https://arxiv.org/abs/1311.0243

import Definitions.Def_BitcoinSelfishMining

theorem BitcoinSelfishMining.stationary_balance (α γ : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2)
    (s : BitcoinSelfishMining.State) :
    BitcoinSelfishMining.stationary α s =
      BitcoinSelfishMining.stateSum
        (fun t => BitcoinSelfishMining.stationary α t * BitcoinSelfishMining.P α γ t s) := by sorry
