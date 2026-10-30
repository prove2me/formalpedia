-- Prove2me | Theorems.Thm_BitcoinSelfishMining_balance_lead
-- name    : BitcoinSelfishMining.balance_lead
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T14:21:17.454106+00:00
-- url     : https://prove2.me/theorems/4123612a-411e-4abf-8162-073e5d905e59
-- title:
--   Balance at states k ≥ 3
-- statement:
--   For $0 < \alpha < 1/2$ and every $n$: $p_{n+3} = \alpha p_{n+2} + (1-\alpha) p_{n+4}$ (in the encoding, `stationary α (lead (n+2)) = α · stationary α (lead (n+1)) + (1-α) · stationary α (lead (n+3))`).
-- source:
--   I. Eyal, E. G. Sirer, Majority is not Enough: Bitcoin Mining is Vulnerable, Financial Cryptography 2014, arXiv:1311.0243, Section 4 (Figure 1, equations (7)-(11)): https://arxiv.org/abs/1311.0243

import Definitions.Def_BitcoinSelfishMining

theorem BitcoinSelfishMining.balance_lead (α : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2) (n : ℕ) :
    BitcoinSelfishMining.stationary α (.lead (n + 2)) =
      α * BitcoinSelfishMining.stationary α (.lead (n + 1))
        + (1 - α) * BitcoinSelfishMining.stationary α (.lead (n + 3)) := by sorry
