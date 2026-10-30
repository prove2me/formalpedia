-- Prove2me | Theorems.Thm_BitcoinSelfishUnique_balance_lead_of
-- name    : BitcoinSelfishUnique.balance_lead_of
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T17:11:11.978231+00:00
-- url     : https://prove2.me/theorems/c7fdc718-686f-4d92-9031-c211d2a40523
-- title:
--   Balance at states k ≥ 3 for any stationary distribution
-- statement:
--   Under the same hypotheses, for every $n$: $\pi_{n+3} = \alpha\pi_{n+2} + (1-\alpha)\pi_{n+4}$.
-- source:
--   I. Eyal, E. G. Sirer, Majority is not Enough: Bitcoin Mining is Vulnerable, Financial Cryptography 2014, arXiv:1311.0243, Section 4, equation (7) (the stationary distribution): https://arxiv.org/abs/1311.0243; the selfish-mining mission's BitcoinSelfishMining (State, P, stateSum, stationary)

import Definitions.Def_BitcoinSelfishUnique
import Definitions.Def_BitcoinSelfishMining
open BitcoinSelfishUnique BitcoinSelfishMining

theorem BitcoinSelfishUnique.balance_lead_of (α γ : ℝ) (π : BitcoinSelfishMining.State → ℝ)
    (h : BitcoinSelfishUnique.IsStationary α γ π) (n : ℕ) :
    π (.lead (n + 2)) = α * π (.lead (n + 1)) + (1 - α) * π (.lead (n + 3)) := by sorry
