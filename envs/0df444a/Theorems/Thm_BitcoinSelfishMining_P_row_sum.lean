-- Prove2me | Theorems.Thm_BitcoinSelfishMining_P_row_sum
-- name    : BitcoinSelfishMining.P_row_sum
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T14:18:41.579498+00:00
-- url     : https://prove2.me/theorems/30122231-acd1-4ebd-a626-d8a3b9ea5319
-- title:
--   The transition matrix is stochastic
-- statement:
--   For all real $\alpha, \gamma$ and every state $s$: `stateSum (fun t => P α γ s t) = 1`. Each row of the chain sums to one (the three outcome probabilities sum to 1 for any $\alpha, \gamma$).
-- source:
--   I. Eyal, E. G. Sirer, Majority is not Enough: Bitcoin Mining is Vulnerable, Financial Cryptography 2014, arXiv:1311.0243, Section 4 (Figure 1, equations (7)-(11)): https://arxiv.org/abs/1311.0243

import Definitions.Def_BitcoinSelfishMining

theorem BitcoinSelfishMining.P_row_sum (α γ : ℝ) (s : BitcoinSelfishMining.State) :
    BitcoinSelfishMining.stateSum (fun t => BitcoinSelfishMining.P α γ s t) = 1 := by sorry
