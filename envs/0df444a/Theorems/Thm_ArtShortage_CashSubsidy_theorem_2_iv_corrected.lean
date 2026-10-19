-- Prove2me | Theorems.Thm_ArtShortage_CashSubsidy_theorem_2_iv_corrected
-- name    : ArtShortage.CashSubsidy.theorem_2_iv_corrected
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:23:44.722459+00:00
-- url     : https://prove2.me/theorems/68dbedf3-350b-45a3-a525-6e06e8e08c5f
-- title:
--   Theorem 2(iv), p. 17 (corrected) — for b > (4 + 2g + g²)/4 the CS Period-1 quantity is max(0, (1 − g)/2, 1 − (b − 1)/g)
-- statement:
--   Fix $0<g<4$ and $1+g<\lambda$. If the government's cash-subsidy budget satisfies $b>(4+2g+g^2)/4$, then the trader's equilibrium Period-1 quantity is unique and equals
--   $$q_1^*=\max\Big\{0,\ \frac{1-g}{2},\ 1-\frac{b-1}{g}\Big\}.$$
--
--   This is the large-budget end of Theorem 2. A large subsidy lets the trader extract the full updated budget in Period 2, so he withholds more in Period 1.
--
--   **Formalization Note** The paper prints $q_1^*=(1-g)/2$. That is false for $(4+2g+g^2)/4<b<1+g(1+g)/2$. In this range the trader's objective $q_1(1-q_1)+\min\big(\sqrt{b(1+g(1-q_1))},\,1+g(1-q_1)\big)$ is maximized at its kink $q_1=1-(b-1)/g$, which lies strictly above $(1-g)/2$. For $g>1$ the printed value is negative, and the constraint $q_1\ge0$ binds. The statement above is the corrected value of the same object.
-- source:
--   Levi, Singhvi & Zheng, Artificial Shortage in Agricultural Supply Chains, SSRN 3332493 (version of 2021-04-14; MSOM forthcoming), p. 17, Theorem 2 (iv) (corrected)

import Mathlib
import Definitions.Def_ArtShortage_CashSubsidy_Model

namespace ArtShortage.CashSubsidy

theorem theorem_2_iv_corrected (g lam : ℝ) (hS : Standing g lam) :
    ∀ b, (4 + 2 * g + g^2) / 4 < b →
      EqQ1 g lam b = {max 0 (max ((1 - g) / 2) (1 - (b - 1) / g))} := by sorry

end ArtShortage.CashSubsidy
