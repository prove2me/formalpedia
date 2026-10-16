-- Prove2me | Theorems.Thm_CustomerVoice_Thresholds_proposition_7
-- name    : CustomerVoice.Thresholds.proposition_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T21:24:58.445421+00:00
-- url     : https://prove2.me/theorems/e147a33a-5a9a-4888-b83e-2cc65395a7a8
-- title:
--   Proposition 7, p. 22 — Δ > Λ iff γ < max{2s/(2s+k), (√(s²+4sk) − s)/(2k)}
-- statement:
--   Let $(\theta_H,\theta_L,\alpha,\gamma,k,s)$ satisfy the standing assumptions $\theta_H>\theta_L>0$, $\alpha,\gamma\in(0,1)$, $k>0$, $s>0$. Let
--   $$\Delta=\max\Big\{\frac{\gamma[2s+(1+\gamma)k]}{(1-\gamma)(2s+\gamma k)},\ \frac{2s+\gamma k}{\gamma k}\Big\}$$
--   be the critical value of $\theta_H/\theta_L$ for informative communication under A-Learning (Proposition 1), and
--   $$\Lambda=\max\Big\{\min\Big\{\frac{\gamma(s+k)}{(1-\gamma)s},\ \frac{1+\gamma}{1-\gamma}\Big\},\ \frac{s}{\gamma k}\Big\}$$
--   the critical value for the cheap-signaling separating equilibrium under O-Learning (Proposition 3). Then
--   $$\Delta>\Lambda\quad\Longleftrightarrow\quad\gamma<\max\Big\{\frac{2s}{2s+k},\ \frac{\sqrt{s^2+4sk}-s}{2k}\Big\}.$$
--
--   In words: customization is harder to sustain through direct communication (A-Learning) than through buyer-proposed designs (O-Learning) exactly when the seller's bargaining power $\gamma$ lies below the stated cutoff; above it the order of the two critical values reverses (or they tie).
--
--   **Formalization Note** The statement is the paper's "(i.e., $\Delta>\Lambda$)" form: $\Delta$ and $\Lambda$ are the printed closed-form thresholds, not infima over equilibria, so the two games do not appear. The square root is `Real.sqrt` of $s^2+4sk>0$. Both sides of the equivalence are strict, as printed.
-- source:
--   Guo, The Voice of Customers in Customization, SSRN working paper 3994319 (version of 2023-11-29, https://ssrn.com/abstract=3994319), p. 22, Proposition 7

import Mathlib
import Definitions.Def_CustomerVoice_Thresholds_Setting

namespace CustomerVoice.Thresholds

theorem proposition_7 (M : Model) (hM : M.Standing) :
    M.Delta > M.Lambda ↔
      M.γ < max (2 * M.s / (2 * M.s + M.k))
        ((Real.sqrt (M.s ^ 2 + 4 * M.s * M.k) - M.s) / (2 * M.k)) := by sorry

end CustomerVoice.Thresholds
