-- Prove2me | Theorems.Thm_BankIntegration_Reversal_customer_effect_signs
-- name    : BankIntegration.Reversal.customer_effect_signs
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T05:03:06.134998+00:00
-- url     : https://prove2.me/theorems/970a911d-0f7f-4fb2-a2b0-f1a3fc05f0ec
-- title:
--   §2.3, p. 10 (PDF 11) — for ξ1 < ξ2, ξ1 < ξ∗ < ξ2 and the bank-customer effect is negative for market 2, positive for market 1
-- statement:
--   Assume the standing assumptions $\lambda>1$, $a_1,a_2,b_1,b_2>0$, $n\ge1$, write $\xi_j=b_j/a_j$ and $\xi^*=(b_1+b_2)/(a_1+a_2)$, and suppose $\xi_1<\xi_2$. Then $\xi_1<\xi^*<\xi_2$, and the bank-customer effects of (11) have opposite signs:
--
--   $$\lambda\cdot\frac{n+1}{n+2}\Big(\frac{1}{1+\xi_2}-\frac{1}{1+\xi^*}\Big)<0<\lambda\cdot\frac{n+1}{n+2}\Big(\frac{1}{1+\xi_1}-\frac{1}{1+\xi^*}\Big).$$
--
--   For the borrower-heavy market 2 the customer effect reinforces the competitor effect; for market 1 it works against it.
-- source:
--   Dam & Sengupta, Bank competition and risk-taking under market integration, Federal Reserve Bank of Kansas City RWP 20-21 (updated Oct. 2024; doi:10.18651/RWP2020-21), §2.3, p. 10 (PDF 11)

import Mathlib
import Definitions.Def_BankIntegration_Reversal_Model

namespace BankIntegration.Reversal

/-- §2.3, p. 10: if `ξ₁ < ξ₂` then `ξ₁ < ξ∗ < ξ₂`, and the bank-customer effect of (11) is
negative with respect to market 2 and positive with respect to market 1. -/
theorem customer_effect_signs (lam a1 a2 b1 b2 : ℝ) (n : ℕ)
    (hS : Standing lam a1 a2 b1 b2 n) (hξ : xi a1 b1 < xi a2 b2) :
    xi a1 b1 < xiStar a1 a2 b1 b2 ∧ xiStar a1 a2 b1 b2 < xi a2 b2 ∧
      bankCustomerEffect lam n (xi a2 b2) (xiStar a1 a2 b1 b2) < 0 ∧
      0 < bankCustomerEffect lam n (xi a1 b1) (xiStar a1 a2 b1 b2) := by sorry

end BankIntegration.Reversal
