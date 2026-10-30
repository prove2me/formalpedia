-- Prove2me | Theorems.Thm_BitcoinSelfishMining_total_mass
-- name    : BitcoinSelfishMining.total_mass
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T14:22:39.834005+00:00
-- url     : https://prove2.me/theorems/599c9a2d-681e-40be-8147-b1f35967eaf7
-- title:
--   The stationary distribution has total mass 1
-- statement:
--   For $0 < \alpha < 1/2$: `stateSum (stationary α) = 1`.
-- source:
--   I. Eyal, E. G. Sirer, Majority is not Enough: Bitcoin Mining is Vulnerable, Financial Cryptography 2014, arXiv:1311.0243, Section 4 (Figure 1, equations (7)-(11)): https://arxiv.org/abs/1311.0243

import Definitions.Def_BitcoinSelfishMining

theorem BitcoinSelfishMining.total_mass (α : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2) :
    BitcoinSelfishMining.stateSum (BitcoinSelfishMining.stationary α) = 1 := by sorry
