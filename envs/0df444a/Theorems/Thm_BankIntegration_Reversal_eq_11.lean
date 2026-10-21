-- Prove2me | Theorems.Thm_BankIntegration_Reversal_eq_11
-- name    : BankIntegration.Reversal.eq_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:03:18.717062+00:00
-- url     : https://prove2.me/theorems/b5559102-9481-492d-85ed-d5e8561de4b5
-- title:
--   Decomposition (11), p. 10 (PDF 11) — r∗ − r_j = bank-competitor effect + bank-customer effect with respect to market j
-- statement:
--   Assume the standing assumptions $\lambda>1$, $a_1,a_2,b_1,b_2>0$, $n\ge1$. Take a Cournot equilibrium of each segmented market $j=1,2$ (with loan rate $r_j$) and a Cournot equilibrium of the integrated market (with loan rate $r^*$). Then for $j=1,2$
--
--   $$r^*-r_j=\underbrace{-\lambda\cdot\frac{1}{1+\xi^*}\Big(\frac{2n+1}{2n+2}-\frac{n+1}{n+2}\Big)}_{\text{bank-competitor effect}}+\underbrace{\lambda\cdot\frac{n+1}{n+2}\Big(\frac{1}{1+\xi_j}-\frac{1}{1+\xi^*}\Big)}_{\text{bank-customer effect with respect to market } j},$$
--
--   where $\xi_j=b_j/a_j$ and $\xi^*=(b_1+b_2)/(a_1+a_2)$.
--
--   The decomposition separates the effect of having more competitor banks ($n\to2n$) from the effect of the change in customer composition ($\xi_j\to\xi^*$).
--
--   **Formalization Note** The loan rates are those of the equilibrium profiles, $r_j=\lambda-L_j/b_j$ and $r^*=\lambda-L/(b_1+b_2)$; the identity is not stated between the closed forms (4) and (9).
-- source:
--   Dam & Sengupta, Bank competition and risk-taking under market integration, Federal Reserve Bank of Kansas City RWP 20-21 (updated Oct. 2024; doi:10.18651/RWP2020-21), p. 10 (PDF 11), (11); (B.1), p. 24 (PDF 25)

import Mathlib
import Definitions.Def_BankIntegration_Reversal_Model

namespace BankIntegration.Reversal

/-- Decomposition (11), p. 10 (= (B.1), p. 24): for Cournot equilibria of the segmented markets
1 and 2 and of the integrated market, `r∗ − r_j` is the bank-competitor effect plus the
bank-customer effect with respect to market `j`, for `j = 1, 2`. -/
theorem eq_11 (lam a1 a2 b1 b2 : ℝ) (n : ℕ) (hS : Standing lam a1 a2 b1 b2 n)
    (L1 L2 : Fin n → ℝ) (LI : Fin (2 * n) → ℝ)
    (h1 : IsCournotEq lam 0 a1 b1 n L1) (h2 : IsCournotEq lam 0 a2 b2 n L2)
    (hI : IsCournotEq lam 0 (a1 + a2) (b1 + b2) (2 * n) LI) :
    loanRate lam (b1 + b2) (∑ i, LI i) - loanRate lam b1 (∑ i, L1 i) =
        bankCompetitorEffect lam n (xiStar a1 a2 b1 b2) +
          bankCustomerEffect lam n (xi a1 b1) (xiStar a1 a2 b1 b2) ∧
      loanRate lam (b1 + b2) (∑ i, LI i) - loanRate lam b2 (∑ i, L2 i) =
        bankCompetitorEffect lam n (xiStar a1 a2 b1 b2) +
          bankCustomerEffect lam n (xi a2 b2) (xiStar a1 a2 b1 b2) := by sorry

end BankIntegration.Reversal
