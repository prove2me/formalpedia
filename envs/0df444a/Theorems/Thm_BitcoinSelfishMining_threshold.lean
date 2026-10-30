-- Prove2me | Theorems.Thm_BitcoinSelfishMining_threshold
-- name    : BitcoinSelfishMining.threshold
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T14:24:32.245815+00:00
-- url     : https://prove2.me/theorems/806647ff-85dd-4895-b153-04e7d99ec709
-- title:
--   Selfish mining beats honest mining exactly above the Eyal–Sirer threshold
-- statement:
--   For $0 < \alpha < 1/2$ and $0 \le \gamma \le 1$: `relativeRevenue α γ > α` if and only if $\alpha > \frac{1-\gamma}{3-2\gamma}$ (equation (11)). The pool's stationary revenue share exceeds its hashrate share exactly when its hashrate exceeds the threshold; $\gamma \ge 0$ is assumed for faithfulness but not used.
-- source:
--   I. Eyal, E. G. Sirer, Majority is not Enough: Bitcoin Mining is Vulnerable, Financial Cryptography 2014, arXiv:1311.0243, Section 4 (Figure 1, equations (7)-(11)): https://arxiv.org/abs/1311.0243

import Definitions.Def_BitcoinSelfishMining

theorem BitcoinSelfishMining.threshold (α γ : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2)
    (_hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    BitcoinSelfishMining.relativeRevenue α γ > α ↔ α > BitcoinSelfishMining.profitThreshold γ := by sorry
