-- Prove2me | Theorems.Thm_BitcoinSelfishMining_denominator_pos
-- name    : BitcoinSelfishMining.denominator_pos
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T14:17:35.401507+00:00
-- url     : https://prove2.me/theorems/a033c18f-a336-4733-b04b-ec4836aa8b92
-- title:
--   The common denominator is positive
-- statement:
--   For $0 < \alpha < 1/2$: $2\alpha^3 - 4\alpha^2 + 1 > 0$.
-- source:
--   I. Eyal, E. G. Sirer, Majority is not Enough: Bitcoin Mining is Vulnerable, Financial Cryptography 2014, arXiv:1311.0243, Section 4 (Figure 1, equations (7)-(11)): https://arxiv.org/abs/1311.0243

import Definitions.Def_BitcoinSelfishMining

theorem BitcoinSelfishMining.denominator_pos (α : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2) :
    0 < 2 * α ^ 3 - 4 * α ^ 2 + 1 := by sorry
