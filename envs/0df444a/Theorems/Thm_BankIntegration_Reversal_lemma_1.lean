-- Prove2me | Theorems.Thm_BankIntegration_Reversal_lemma_1
-- name    : BankIntegration.Reversal.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:03:11.536998+00:00
-- url     : https://prove2.me/theorems/b99f8abc-49c1-43c1-8a9f-70f9df17e8eb
-- title:
--   Lemma 1, p. 8 (PDF 9) — unique Cournot equilibrium of segmented market j, with deposit rate (3), loan rate (4), risk-shifting (5)
-- statement:
--   Let $\lambda>1$ and consider the segmented market $j$, with $a_j>0$ depositors, $b_j>0$ borrowers, $n\ge1$ banks and no lending cost: bank $i$ chooses $L_{ij}\ge0$ to maximize display (2),
--   $$\frac{L_j}{2\lambda b_j}\Big(\lambda-\frac{L_j}{b_j}-\frac{L_j}{a_j}\Big)L_{ij},\qquad L_j=\sum_k L_{kj}.$$
--   Write $\xi_j=b_j/a_j$. Then the Cournot game has exactly one equilibrium; in every equilibrium $L_j=nL_{ij}$ for all $i$; and the deposit rate $R_j=L_j/a_j$, the loan rate $r_j=\lambda-L_j/b_j$ and the borrower-optimal risk are
--
--   $$R_j=\lambda\cdot\frac{n+1}{n+2}\cdot\frac{\xi_j}{1+\xi_j},\qquad r_j=\lambda\Big(1-\frac{n+1}{n+2}\cdot\frac{1}{1+\xi_j}\Big),\qquad \theta_j=\lambda\Big(1-\frac12\cdot\frac{n+1}{n+2}\cdot\frac{1}{1+\xi_j}\Big),$$
--
--   where $\theta_j$ is the unique borrower-optimal risk at $r_j$.
--
--   This is the segmented market equilibrium (SME) against which integration is compared.
--
--   **Formalization Note** "Unique symmetric equilibrium wherein $L_j=nL_{ij}$" is stated as: there is exactly one equilibrium, and every equilibrium satisfies $L_j=nL_{ij}$ for all $i$. Banks are indexed by `Fin n`.
-- source:
--   Dam & Sengupta, Bank competition and risk-taking under market integration, Federal Reserve Bank of Kansas City RWP 20-21 (updated Oct. 2024; doi:10.18651/RWP2020-21), p. 8 (PDF 9), Lemma 1, (3)–(5); proof B.1, p. 24 (PDF 25)

import Mathlib
import Definitions.Def_BankIntegration_Reversal_Model

namespace BankIntegration.Reversal

/-- Lemma 1, p. 8: the segmented market `j`, with `a_j` depositors, `b_j` borrowers, `n ≥ 1` banks
and no lending cost, has a unique Cournot equilibrium; in every equilibrium `L_j = n L_ij` for all
banks `i`, and the deposit rate, loan rate and borrower-optimal risk are (3), (4), (5), with
`ξ_j = b_j/a_j`. -/
theorem lemma_1 (lam aj bj : ℝ) (n : ℕ) (hlam : 1 < lam) (ha : 0 < aj) (hb : 0 < bj)
    (hn : 1 ≤ n) :
    (∃! L : Fin n → ℝ, IsCournotEq lam 0 aj bj n L) ∧
    ∀ L : Fin n → ℝ, IsCournotEq lam 0 aj bj n L →
      (∀ i, ∑ k, L k = (n : ℝ) * L i) ∧
      depositRate aj (∑ k, L k) =
        lam * (((n : ℝ) + 1) / ((n : ℝ) + 2)) * (xi aj bj / (1 + xi aj bj)) ∧
      loanRate lam bj (∑ k, L k) =
        lam * (1 - ((n : ℝ) + 1) / ((n : ℝ) + 2) * (1 / (1 + xi aj bj))) ∧
      ∀ θ : ℝ, IsOptimalRisk lam (loanRate lam bj (∑ k, L k)) θ ↔
        θ = lam * (1 - 1 / 2 * (((n : ℝ) + 1) / ((n : ℝ) + 2)) * (1 / (1 + xi aj bj))) := by sorry

end BankIntegration.Reversal
