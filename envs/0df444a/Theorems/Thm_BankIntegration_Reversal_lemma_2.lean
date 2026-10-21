-- Prove2me | Theorems.Thm_BankIntegration_Reversal_lemma_2
-- name    : BankIntegration.Reversal.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:03:27.242555+00:00
-- url     : https://prove2.me/theorems/7beaac1d-c954-4d83-8898-f0e5caf93f8f
-- title:
--   Lemma 2, p. 9 (PDF 10) — unique Cournot equilibrium of the integrated market, with (8), (9), (10), and ξ∗ ∈ (ξ1, ξ2)
-- statement:
--   Assume the standing assumptions: $\lambda>1$, $a_1,a_2,b_1,b_2>0$, $n\ge1$. The integrated market has $a_1+a_2$ depositors, $b_1+b_2$ borrowers and $2n$ banks without lending cost; bank $i$ chooses $L_i\ge0$ to maximize display (7),
--   $$\frac{L}{2\lambda(b_1+b_2)}\Big(\lambda-\frac{L}{b_1+b_2}-\frac{L}{a_1+a_2}\Big)L_i,\qquad L=\sum_k L_k .$$
--   Write $\xi^*=(b_1+b_2)/(a_1+a_2)$. Then the Cournot game has exactly one equilibrium; in every equilibrium $L=2nL_i$ for all $i$; and the deposit rate $R^*=L/(a_1+a_2)$, the loan rate $r^*=\lambda-L/(b_1+b_2)$ and the borrower-optimal risk are
--
--   $$R^*=\lambda\cdot\frac{2n+1}{2n+2}\cdot\frac{\xi^*}{1+\xi^*},\qquad r^*=\lambda\Big(1-\frac{2n+1}{2n+2}\cdot\frac{1}{1+\xi^*}\Big),\qquad \theta^*=\lambda\Big(1-\frac12\cdot\frac{2n+1}{2n+2}\cdot\frac{1}{1+\xi^*}\Big),$$
--
--   where $\theta^*$ is the unique borrower-optimal risk at $r^*$. Moreover, if $\xi_1<\xi_2$ (with $\xi_j=b_j/a_j$), then $\xi_1<\xi^*<\xi_2$.
--
--   This is the integrated market equilibrium (IME).
--
--   **Formalization Note** Banks are indexed by `Fin (2 * n)`. The page's "$\xi^*\in(\xi_1,\xi_2)$" uses the section's labelling $\xi_1<\xi_2$ (p. 7); it is stated as an implication from that hypothesis.
-- source:
--   Dam & Sengupta, Bank competition and risk-taking under market integration, Federal Reserve Bank of Kansas City RWP 20-21 (updated Oct. 2024; doi:10.18651/RWP2020-21), p. 9 (PDF 10), Lemma 2, (8)–(10); proof B.3, p. 24 (PDF 25)

import Mathlib
import Definitions.Def_BankIntegration_Reversal_Model

namespace BankIntegration.Reversal

/-- Lemma 2, p. 9: the integrated market, with `a₁ + a₂` depositors, `b₁ + b₂` borrowers, `2n`
banks and no lending cost, has a unique Cournot equilibrium; in every equilibrium `L = 2n L_i` for
all banks `i`, and the deposit rate, loan rate and borrower-optimal risk are (8), (9), (10), with
`ξ∗ = (b₁ + b₂)/(a₁ + a₂)`; and `ξ∗ ∈ (ξ₁, ξ₂)` when `ξ₁ < ξ₂`. -/
theorem lemma_2 (lam a1 a2 b1 b2 : ℝ) (n : ℕ) (hS : Standing lam a1 a2 b1 b2 n) :
    (∃! L : Fin (2 * n) → ℝ, IsCournotEq lam 0 (a1 + a2) (b1 + b2) (2 * n) L) ∧
    (∀ L : Fin (2 * n) → ℝ, IsCournotEq lam 0 (a1 + a2) (b1 + b2) (2 * n) L →
      (∀ i, ∑ k, L k = 2 * (n : ℝ) * L i) ∧
      depositRate (a1 + a2) (∑ k, L k) =
        lam * ((2 * (n : ℝ) + 1) / (2 * (n : ℝ) + 2)) *
          (xiStar a1 a2 b1 b2 / (1 + xiStar a1 a2 b1 b2)) ∧
      loanRate lam (b1 + b2) (∑ k, L k) =
        lam * (1 - (2 * (n : ℝ) + 1) / (2 * (n : ℝ) + 2) * (1 / (1 + xiStar a1 a2 b1 b2))) ∧
      ∀ θ : ℝ, IsOptimalRisk lam (loanRate lam (b1 + b2) (∑ k, L k)) θ ↔
        θ = lam * (1 - 1 / 2 * ((2 * (n : ℝ) + 1) / (2 * (n : ℝ) + 2)) *
          (1 / (1 + xiStar a1 a2 b1 b2)))) ∧
    (xi a1 b1 < xi a2 b2 →
      xi a1 b1 < xiStar a1 a2 b1 b2 ∧ xiStar a1 a2 b1 b2 < xi a2 b2) := by sorry

end BankIntegration.Reversal
