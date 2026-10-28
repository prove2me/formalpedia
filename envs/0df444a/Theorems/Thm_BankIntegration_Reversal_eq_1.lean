-- Prove2me | Theorems.Thm_BankIntegration_Reversal_eq_1
-- name    : BankIntegration.Reversal.eq_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T05:03:02.46799+00:00
-- url     : https://prove2.me/theorems/126040a9-7e88-43de-a8c5-f1e854dc0251
-- title:
--   Equation (1), p. 7 (PDF 8) — the borrower-optimal risk at loan rate r is θ(r) = (λ + r)/2
-- statement:
--   Let $\lambda>1$ and let $r$ be a loan rate with $-\lambda\le r\le\lambda$. A borrower choosing the risk $\theta\in[0,\lambda]$ of a project that returns $\theta$ with probability $1-\theta/\lambda$ and pays the loan rate $r$ solves $\max_{\theta\in[0,\lambda]}(1-\theta/\lambda)(\theta-r)$. This problem has exactly one solution, namely
--
--   $$\theta(r)=\frac{\lambda+r}{2}.$$
--
--   This is the incentive-compatibility constraint (1): higher loan rates make borrowers take higher risk. Every statement about risk-taking in the mission passes through it.
--
--   **Formalization Note** The range $-\lambda\le r\le\lambda$ is added: it is exactly the range in which $(\lambda+r)/2$ lies in $[0,\lambda]$, and every equilibrium loan rate of the model lies in it. The statement is an equivalence: $\theta$ is borrower-optimal if and only if $\theta=(\lambda+r)/2$.
-- source:
--   Dam & Sengupta, Bank competition and risk-taking under market integration, Federal Reserve Bank of Kansas City RWP 20-21 (updated Oct. 2024; doi:10.18651/RWP2020-21), p. 7 (PDF 8), equation (1)

import Mathlib
import Definitions.Def_BankIntegration_Reversal_Model

namespace BankIntegration.Reversal

/-- Equation (1), p. 7: at a loan rate `r` with `−λ ≤ r ≤ λ`, the borrower-optimal risk is
unique and equals `θ(r) = (λ + r)/2`. -/
theorem eq_1 (lam r θ : ℝ) (hlam : 1 < lam) (hr0 : -lam ≤ r) (hr1 : r ≤ lam) :
    IsOptimalRisk lam r θ ↔ θ = (lam + r) / 2 := by sorry

end BankIntegration.Reversal
