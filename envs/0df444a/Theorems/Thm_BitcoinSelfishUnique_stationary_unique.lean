-- Prove2me | Theorems.Thm_BitcoinSelfishUnique_stationary_unique
-- name    : BitcoinSelfishUnique.stationary_unique
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T17:12:22.247978+00:00
-- url     : https://prove2.me/theorems/5f354012-d509-41d8-a432-c84188120a6c
-- title:
--   The stationary distribution is unique
-- statement:
--   For $0 < \alpha < 1/2$, any $\gamma$, and any $\pi$ with `IsStationary α γ π`: $\pi(s) = $ `stationary α s` for every state $s$. With the geometric form, the balance equations at $0'$ and $1$ express every value through $\pi_0$, and total mass 1 fixes $\pi_0 = (1-2\alpha)/(2\alpha^3 - 4\alpha^2 + 1)$, the paper's equation (7). Together with the selfish-mining mission this makes the revenue analysis a statement about the chain's only stationary distribution.
-- source:
--   I. Eyal, E. G. Sirer, Majority is not Enough: Bitcoin Mining is Vulnerable, Financial Cryptography 2014, arXiv:1311.0243, Section 4, equation (7) (the stationary distribution): https://arxiv.org/abs/1311.0243; the selfish-mining mission's BitcoinSelfishMining (State, P, stateSum, stationary)

import Definitions.Def_BitcoinSelfishUnique
import Definitions.Def_BitcoinSelfishMining
open BitcoinSelfishUnique BitcoinSelfishMining

theorem BitcoinSelfishUnique.stationary_unique (α γ : ℝ) (π : BitcoinSelfishMining.State → ℝ)
    (h0 : 0 < α) (h1 : α < 1 / 2) (h : BitcoinSelfishUnique.IsStationary α γ π)
    (s : BitcoinSelfishMining.State) : π s = BitcoinSelfishMining.stationary α s := by sorry
