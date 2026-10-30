-- Prove2me | Theorems.Thm_BitcoinSelfishUnique_geometric_of_isStationary
-- name    : BitcoinSelfishUnique.geometric_of_isStationary
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T17:11:41.480078+00:00
-- url     : https://prove2.me/theorems/4c018b4a-9a60-4fcc-884e-0f83107d4deb
-- title:
--   Every stationary distribution is geometric on the leads
-- statement:
--   For $0 < \alpha < 1/2$ and `IsStationary α γ π`: for every $n$, $\pi(\text{lead}(n+1)) = \frac{\alpha}{1-\alpha}\,\pi(\text{lead } n)$. The second-order balance recurrence has the general solution $A + B r^n$ with $r = \alpha/(1-\alpha)$; summability forces $A = 0$.
-- source:
--   I. Eyal, E. G. Sirer, Majority is not Enough: Bitcoin Mining is Vulnerable, Financial Cryptography 2014, arXiv:1311.0243, Section 4, equation (7) (the stationary distribution): https://arxiv.org/abs/1311.0243; the selfish-mining mission's BitcoinSelfishMining (State, P, stateSum, stationary)

import Definitions.Def_BitcoinSelfishUnique
import Definitions.Def_BitcoinSelfishMining
open BitcoinSelfishUnique BitcoinSelfishMining

theorem BitcoinSelfishUnique.geometric_of_isStationary (α γ : ℝ)
    (π : BitcoinSelfishMining.State → ℝ) (h0 : 0 < α) (h1 : α < 1 / 2)
    (h : BitcoinSelfishUnique.IsStationary α γ π) (n : ℕ) :
    π (.lead (n + 1)) = α / (1 - α) * π (.lead n) := by sorry
