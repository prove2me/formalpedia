-- Prove2me | Theorems.Thm_BankIntegration_Reversal_proposition_2
-- name    : BankIntegration.Reversal.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:03:13.707632+00:00
-- url     : https://prove2.me/theorems/9578d83c-0e71-4b26-99b8-c05dfd29e22d
-- title:
--   Proposition 2, pp. 10–11 (PDF 11–12) — with ξ1 < ξ2, IME loan rate and risk-taking fall below market 2's SME; in market 1 they fall or rise as the bank-customer effect is weak or strong
-- statement:
--   Two banking markets $j=1,2$ have $a_j>0$ depositors, $b_j>0$ borrowers and $n\ge1$ banks each, and $\lambda>1$. Write $\xi_j=b_j/a_j$ and suppose market 2 has the higher ratio of borrowers to depositors, $\xi_1<\xi_2$. Let $r_1,r_2$ be the loan rates of Cournot equilibria of the segmented markets (display (2)), $r^*$ the loan rate of a Cournot equilibrium of the integrated market with $a_1+a_2$ depositors, $b_1+b_2$ borrowers and $2n$ banks (display (7)), and $\theta_1,\theta_2,\theta^*$ borrower-optimal risks at these rates. With $\xi^*=(b_1+b_2)/(a_1+a_2)$ put
--
--   $$C=-\lambda\cdot\frac{1}{1+\xi^*}\Big(\frac{2n+1}{2n+2}-\frac{n+1}{n+2}\Big),\qquad B_1=\lambda\cdot\frac{n+1}{n+2}\Big(\frac{1}{1+\xi_1}-\frac{1}{1+\xi^*}\Big),$$
--
--   the bank-competitor effect and the bank-customer effect with respect to market 1. Then the integrated-market (IME) loan rate and risk-taking
--
--   1. (a) are always lower than their segmented-market (SME) values in market 2: $r^*<r_2$ and $\theta^*<\theta_2$;
--   2. (b-i) are lower than their SME values in market 1, $r^*<r_1$ and $\theta^*<\theta_1$, if the positive bank-customer effect is sufficiently weak, $B_1<-C$;
--   3. (b-ii) are higher than their SME values in market 1, $r^*>r_1$ and $\theta^*>\theta_1$, if it is sufficiently strong, $B_1>-C$.
--
--   The result shows that market integration, although it doubles the number of competing banks, can raise loan rates and borrower risk-taking in the depositor-heavy market.
--
--   **Formalization Note** "Sufficiently weak/strong" is read as the comparison of the two terms of (11), as on p. 10 and in B.4; the case $B_1=-C$ is left open, as on the page. The statement covers every Cournot equilibrium of each market (Lemmas 1 and 2 show there is exactly one) and every borrower-optimal risk at each rate (equation (1) shows it is unique). Equilibrium volumes are restricted to $L\ge0$.
-- source:
--   Dam & Sengupta, Bank competition and risk-taking under market integration, Federal Reserve Bank of Kansas City RWP 20-21 (updated Oct. 2024; doi:10.18651/RWP2020-21), pp. 10–11 (PDF 11–12), Proposition 2; proof B.4, p. 24 (PDF 25)

import Mathlib
import Definitions.Def_BankIntegration_Reversal_Model

namespace BankIntegration.Reversal

/-- Proposition 2, pp. 10–11: let `ξ₁ < ξ₂`, and take Cournot equilibria of the segmented markets
1, 2 (loan rates `r₁`, `r₂`) and of the integrated market (loan rate `r∗`), and borrower-optimal
risks `θ₁`, `θ₂`, `θ∗` at these rates. (a) `r∗ < r₂` and `θ∗ < θ₂`. (b-i) If the positive
bank-customer effect with respect to market 1 is weaker than the (negative) bank-competitor effect
in absolute value, `r∗ < r₁` and `θ∗ < θ₁`. (b-ii) If it is stronger, `r∗ > r₁` and `θ∗ > θ₁`. -/
theorem proposition_2 (lam a1 a2 b1 b2 : ℝ) (n : ℕ) (hS : Standing lam a1 a2 b1 b2 n)
    (hξ : xi a1 b1 < xi a2 b2)
    (L1 L2 : Fin n → ℝ) (LI : Fin (2 * n) → ℝ)
    (h1 : IsCournotEq lam 0 a1 b1 n L1) (h2 : IsCournotEq lam 0 a2 b2 n L2)
    (hI : IsCournotEq lam 0 (a1 + a2) (b1 + b2) (2 * n) LI) :
    let r1 := loanRate lam b1 (∑ i, L1 i)
    let r2 := loanRate lam b2 (∑ i, L2 i)
    let rS := loanRate lam (b1 + b2) (∑ i, LI i)
    let comp := bankCompetitorEffect lam n (xiStar a1 a2 b1 b2)
    let cust1 := bankCustomerEffect lam n (xi a1 b1) (xiStar a1 a2 b1 b2)
    (rS < r2 ∧
        ∀ θS θ2, IsOptimalRisk lam rS θS → IsOptimalRisk lam r2 θ2 → θS < θ2) ∧
      (cust1 < -comp → rS < r1 ∧
        ∀ θS θ1, IsOptimalRisk lam rS θS → IsOptimalRisk lam r1 θ1 → θS < θ1) ∧
      (-comp < cust1 → r1 < rS ∧
        ∀ θS θ1, IsOptimalRisk lam rS θS → IsOptimalRisk lam r1 θ1 → θ1 < θS) := by sorry

end BankIntegration.Reversal
