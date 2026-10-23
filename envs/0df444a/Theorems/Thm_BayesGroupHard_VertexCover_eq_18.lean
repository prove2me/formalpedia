-- Prove2me | Theorems.Thm_BayesGroupHard_VertexCover_eq_18
-- name    : BayesGroupHard.VertexCover.eq_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:18:35.620121+00:00
-- url     : https://prove2.me/theorems/1be7c483-9783-4402-a021-b9231fe6ae79
-- title:
--   (18), §A.2, p. 30 — YES case: $\phi_{i,2} < n\tilde q(0.998) + \log(1 + (0.41/0.42)^n) - \frac n2(\tilde q(0.999) + \tilde q(0.998))$
-- statement:
--   In the vertex-cover network of a graph $G$ on $n$ vertices, let $\kappa$'s signal structure $0 < k_0, k_1 < 1$ satisfy $\log(k_1/k_0) = \lambda_\kappa(0) = -\frac n2(\tilde q(0.998) + \tilde q(0.999))$, and let $s$ be a signal profile with the reduction's history ($a_{\varepsilon,1} = 1$ for all edge agents, $a_{\kappa,0} = 0$). If $G$ has a vertex cover $\Sigma^\star$ with $|\Sigma^\star| \le 0.85n$ (the YES case), then
--   $$\phi_{i,2} < n\,\tilde q(0.998) + \log\Bigl(1 + \Bigl(\frac{0.41}{0.42}\Bigr)^n\Bigr) - \frac n2\bigl(\tilde q(0.999) + \tilde q(0.998)\bigr).$$
--
--   The right-hand side equals $-\frac n2(\tilde q(0.999) - \tilde q(0.998)) + \log(1 + (0.41/0.42)^n)$, which is $-\Omega(n)$; so agent $i$'s belief in state $1$ is exponentially small in the YES case.
--
--   **Formalization Note.** The explicit right-hand side of (18) is stated, not its consequence "$< -\Omega(n)$".
-- source:
--   Hązła, Jadbabaie, Mossel & Rahimian, Bayesian Decision Making in Groups is Hard, arXiv:1705.04770v4, p. 30, §A.2, (18) (YES hypothesis p. 29)

import Mathlib
import Definitions.Def_BayesGroupHard_VertexCover_Model

open Finset

namespace BayesGroupHard.VertexCover

/-- (18), §A.2, p. 30 (YES case): if some vertex cover has at most `0.85 n` vertices and
`λ_κ(0) = -(n/2)(q̃(0.998) + q̃(0.999))`, then
`φ_{i,2} < n q̃(0.998) + log(1 + (0.41/0.42)^n) - (n/2)(q̃(0.999) + q̃(0.998))`. -/
theorem eq_18 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k₀ k₁ : ℝ)
    (hk₀ : 0 < k₀) (hk₀' : k₀ < 1) (hk₁ : 0 < k₁) (hk₁' : k₁ < 1)
    (hlam : Real.log (k₁ / k₀) = lamKappa0 n)
    (hYES : ∃ C : Finset (Fin n), G.IsVertexCover (C : Set (Fin n)) ∧
      (C.card : ℝ) ≤ 85 / 100 * n)
    (s : Agent n G → Bool)
    (hedg : ∀ e : G.edgeSet, act (vcNet G k₀ k₁) 1 (Agent.edg e) s = true)
    (hkap : act (vcNet G k₀ k₁) 0 Agent.kap s = false) :
    logBelief (vcNet G k₀ k₁) 2 Agent.iAg s <
      (n : ℝ) * qtil (998 / 1000) + Real.log (1 + (41 / 42 : ℝ) ^ n) -
        (n : ℝ) / 2 * (qtil (999 / 1000) + qtil (998 / 1000)) := by sorry

end BayesGroupHard.VertexCover
