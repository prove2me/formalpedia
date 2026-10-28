-- Prove2me | Theorems.Thm_BankIntegration_Reversal_competitor_effect_neg
-- name    : BankIntegration.Reversal.competitor_effect_neg
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T05:03:04.090001+00:00
-- url     : https://prove2.me/theorems/eeb6a9d6-0edf-4ce2-aef0-56a2699af456
-- title:
--   §2.3, p. 10 (PDF 11) — the bank-competitor effect is always negative
-- statement:
--   Assume the standing assumptions $\lambda>1$, $a_1,a_2,b_1,b_2>0$, $n\ge1$, and let $\xi^*=(b_1+b_2)/(a_1+a_2)$. Then the bank-competitor effect of (11) is negative:
--
--   $$-\lambda\cdot\frac{1}{1+\xi^*}\Big(\frac{2n+1}{2n+2}-\frac{n+1}{n+2}\Big)<0 .$$
--
--   Doubling the number of competitor banks always pushes loan rates down; this is the within-market competition channel.
-- source:
--   Dam & Sengupta, Bank competition and risk-taking under market integration, Federal Reserve Bank of Kansas City RWP 20-21 (updated Oct. 2024; doi:10.18651/RWP2020-21), §2.3, p. 10 (PDF 11)

import Mathlib
import Definitions.Def_BankIntegration_Reversal_Model

namespace BankIntegration.Reversal

/-- §2.3, p. 10: the bank-competitor effect of (11) is always negative. -/
theorem competitor_effect_neg (lam a1 a2 b1 b2 : ℝ) (n : ℕ)
    (hS : Standing lam a1 a2 b1 b2 n) :
    bankCompetitorEffect lam n (xiStar a1 a2 b1 b2) < 0 := by sorry

end BankIntegration.Reversal
