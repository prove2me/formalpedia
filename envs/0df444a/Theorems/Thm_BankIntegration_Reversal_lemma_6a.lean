-- Prove2me | Theorems.Thm_BankIntegration_Reversal_lemma_6a
-- name    : BankIntegration.Reversal.lemma_6a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:03:07.577138+00:00
-- url     : https://prove2.me/theorems/7aaeb918-4cb3-41ff-86b5-61177390d3f1
-- title:
--   Lemma 6(a), p. 22 (PDF 23) — unique Cournot equilibrium with cost c, L = nL_i, and the rates and risk (A.4)–(A.6)
-- statement:
--   Consider a banking market with $a>0$ depositors, $b>0$ borrowers, $m\ge1$ banks and marginal lending cost $c$ with $0\le c<\lambda$, where $\lambda>1$. Bank $i$ chooses its loan volume $L_i\ge0$ to maximize
--   $$\frac{L}{2\lambda b}\Big(\lambda-\frac{L}{b}-\frac{L}{a}-c\Big)L_i,\qquad L=\sum_k L_k .$$
--   Write $\xi=b/a$. Then:
--
--   1. the Cournot game has exactly one equilibrium;
--   2. in every equilibrium, $L=mL_i$ for every bank $i$;
--   3. in every equilibrium the deposit rate $R=L/a$, the loan rate $r=\lambda-L/b$ and the borrower-optimal risk at $r$ are
--   $$R=(\lambda-c)\cdot\frac{m+1}{m+2}\cdot\frac{\xi}{1+\xi},\qquad r=\lambda-(\lambda-c)\cdot\frac{m+1}{m+2}\cdot\frac{1}{1+\xi},\qquad \theta=\lambda-\frac{\lambda-c}{2}\cdot\frac{m+1}{m+2}\cdot\frac{1}{1+\xi},$$
--   and $\theta$ given by the last formula is the only borrower-optimal risk at $r$.
--
--   This is the base equilibrium of the paper: Lemmas 1 and 2 are its special cases $c=0$ with $n$ and $2n$ banks.
--
--   **Formalization Note** The page assumes $n\ge2$ banks in Appendix A; the statement is made for $m\ge1$ because Lemma 1 applies it with a single bank per market allowed (p. 6, $n\ge1$). The hypothesis $c<\lambda$ is added: the page leaves it implicit, and for $c>\lambda$ the closed form would be a negative volume. Equilibrium means a global best response over all volumes $x\ge0$, not only the first-order condition (A.7).
-- source:
--   Dam & Sengupta, Bank competition and risk-taking under market integration, Federal Reserve Bank of Kansas City RWP 20-21 (updated Oct. 2024; doi:10.18651/RWP2020-21), p. 22 (PDF 23), Lemma 6(a), (A.4)–(A.6); proof p. 23 (PDF 24)

import Mathlib
import Definitions.Def_BankIntegration_Reversal_Model

namespace BankIntegration.Reversal

/-- Lemma 6(a), p. 22: a market with `a` depositors, `b` borrowers, `m ≥ 1` banks and marginal
lending cost `0 ≤ c < λ` has a unique Cournot equilibrium; in every equilibrium `L = m L_i` for all
banks `i`, and the deposit rate, loan rate and borrower-optimal risk are (A.4), (A.5), (A.6),
with `ξ = b/a`. -/
theorem lemma_6a (lam c a b : ℝ) (m : ℕ) (hlam : 1 < lam) (hc0 : 0 ≤ c) (hc1 : c < lam)
    (ha : 0 < a) (hb : 0 < b) (hm : 1 ≤ m) :
    (∃! L : Fin m → ℝ, IsCournotEq lam c a b m L) ∧
    ∀ L : Fin m → ℝ, IsCournotEq lam c a b m L →
      (∀ i, ∑ k, L k = (m : ℝ) * L i) ∧
      depositRate a (∑ k, L k) =
        (lam - c) * (((m : ℝ) + 1) / ((m : ℝ) + 2)) * (xi a b / (1 + xi a b)) ∧
      loanRate lam b (∑ k, L k) =
        lam - (lam - c) * (((m : ℝ) + 1) / ((m : ℝ) + 2)) * (1 / (1 + xi a b)) ∧
      ∀ θ : ℝ, IsOptimalRisk lam (loanRate lam b (∑ k, L k)) θ ↔
        θ = lam - (lam - c) / 2 * (((m : ℝ) + 1) / ((m : ℝ) + 2)) * (1 / (1 + xi a b)) := by sorry

end BankIntegration.Reversal
