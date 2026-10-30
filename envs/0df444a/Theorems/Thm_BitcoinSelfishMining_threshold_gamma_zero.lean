-- Prove2me | Theorems.Thm_BitcoinSelfishMining_threshold_gamma_zero
-- name    : BitcoinSelfishMining.threshold_gamma_zero
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T14:24:53.988124+00:00
-- url     : https://prove2.me/theorems/e326859d-39ca-4f4f-aa5b-23089451c701
-- title:
--   With no honest miners on the pool's branch, the threshold is 1/3
-- statement:
--   For $0 < \alpha < 1/2$: `relativeRevenue α 0 > α` iff $\alpha > 1/3$.
-- source:
--   I. Eyal, E. G. Sirer, Majority is not Enough: Bitcoin Mining is Vulnerable, Financial Cryptography 2014, arXiv:1311.0243, Section 4 (Figure 1, equations (7)-(11)): https://arxiv.org/abs/1311.0243

import Definitions.Def_BitcoinSelfishMining

theorem BitcoinSelfishMining.threshold_gamma_zero (α : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2) :
    BitcoinSelfishMining.relativeRevenue α 0 > α ↔ α > 1 / 3 := by sorry
