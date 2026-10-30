-- Prove2me | Theorems.Thm_BitcoinSelfishUnique_stationary_isStationary
-- name    : BitcoinSelfishUnique.stationary_isStationary
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T17:08:26.369402+00:00
-- url     : https://prove2.me/theorems/3886879d-ee26-437b-88a3-34a95c41edf8
-- title:
--   The paper's distribution is a stationary distribution
-- statement:
--   For $0 < \alpha < 1/2$ and any $\gamma$: `IsStationary α γ (stationary α)`. Nonnegativity, summability over the leads, total mass 1 and invariance, re-proved from the definitions.
-- source:
--   I. Eyal, E. G. Sirer, Majority is not Enough: Bitcoin Mining is Vulnerable, Financial Cryptography 2014, arXiv:1311.0243, Section 4, equation (7) (the stationary distribution): https://arxiv.org/abs/1311.0243; the selfish-mining mission's BitcoinSelfishMining (State, P, stateSum, stationary)

import Definitions.Def_BitcoinSelfishUnique
import Definitions.Def_BitcoinSelfishMining
open BitcoinSelfishUnique BitcoinSelfishMining

theorem BitcoinSelfishUnique.stationary_isStationary (α γ : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2) :
    BitcoinSelfishUnique.IsStationary α γ (BitcoinSelfishMining.stationary α) := by sorry
