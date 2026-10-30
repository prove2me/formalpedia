-- Prove2me | Theorems.Thm_BitcoinSelfishMining_tail_sum
-- name    : BitcoinSelfishMining.tail_sum
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T14:22:18.376805+00:00
-- url     : https://prove2.me/theorems/fe7906ea-4369-4d8b-bf16-354dc909c089
-- title:
--   The tail of the distribution in closed form
-- statement:
--   For $0 < \alpha < 1/2$: $\sum'_{n} p_{\text{lead}(n+2)} = p_1 \left(\frac{\alpha}{1-\alpha}\right)^2 \frac{1-\alpha}{1-2\alpha}$. A geometric series with ratio $\alpha/(1-\alpha) < 1$.
-- source:
--   I. Eyal, E. G. Sirer, Majority is not Enough: Bitcoin Mining is Vulnerable, Financial Cryptography 2014, arXiv:1311.0243, Section 4 (Figure 1, equations (7)-(11)): https://arxiv.org/abs/1311.0243

import Definitions.Def_BitcoinSelfishMining

theorem BitcoinSelfishMining.tail_sum (α : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2) :
    ∑' n : ℕ, BitcoinSelfishMining.stationary α (.lead (n + 2)) =
      BitcoinSelfishMining.stationary α (.lead 0) * (α / (1 - α)) ^ 2 * (1 - α) / (1 - 2 * α) := by sorry
