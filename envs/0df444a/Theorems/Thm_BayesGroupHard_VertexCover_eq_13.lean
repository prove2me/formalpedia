-- Prove2me | Theorems.Thm_BayesGroupHard_VertexCover_eq_13
-- name    : BayesGroupHard.VertexCover.eq_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:18:27.219427+00:00
-- url     : https://prove2.me/theorems/5de8a556-78ab-42bd-8747-7a830f33f27c
-- title:
--   (13), §A.1, p. 29 — NO case: $\phi_{i,2} > \frac n2(\tilde q(0.999) - \tilde q(0.998))$
-- statement:
--   In the vertex-cover network of a graph $G$ on $n$ vertices, let $\kappa$'s signal structure $0 < k_0, k_1 < 1$ satisfy
--   $$\log\frac{k_1}{k_0} = \lambda_\kappa(0) = -\frac n2\bigl(\tilde q(0.998) + \tilde q(0.999)\bigr),$$
--   and let $s$ be a signal profile with the reduction's history ($a_{\varepsilon,1} = 1$ for all edge agents, $a_{\kappa,0} = 0$). If every vertex cover $\hat\Sigma$ of $G$ has $|\hat\Sigma| > 0.999n$ (the NO case), then
--   $$\phi_{i,2} > \frac n2\bigl(\tilde q(0.999) - \tilde q(0.998)\bigr).$$
--   Here $\tilde q(\alpha) = \log(\bar q(\alpha)/\underline q(\alpha)) = \alpha\log(14/9) - \log(7/6)$.
--
--   Since the right-hand side is a positive multiple of $n$, agent $i$'s belief in state $0$ is exponentially small in the NO case.
--
--   **Formalization Note.** The strict "$> 0.999n$" is §A.1's (and Theorem 5's) form; Theorem 6 uses "at least $0.999n$".
-- source:
--   Hązła, Jadbabaie, Mossel & Rahimian, Bayesian Decision Making in Groups is Hard, arXiv:1705.04770v4, p. 29, §A.1, (13)

import Mathlib
import Definitions.Def_BayesGroupHard_VertexCover_Model

open Finset

namespace BayesGroupHard.VertexCover

/-- (13), §A.1, p. 29 (NO case): if every vertex cover has more than `0.999 n` vertices and
`λ_κ(0) = -(n/2)(q̃(0.998) + q̃(0.999))`, then `φ_{i,2} > (n/2)(q̃(0.999) - q̃(0.998))`. -/
theorem eq_13 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k₀ k₁ : ℝ)
    (hk₀ : 0 < k₀) (hk₀' : k₀ < 1) (hk₁ : 0 < k₁) (hk₁' : k₁ < 1)
    (hlam : Real.log (k₁ / k₀) = lamKappa0 n)
    (hNO : ∀ C : Finset (Fin n), G.IsVertexCover (C : Set (Fin n)) →
      999 / 1000 * (n : ℝ) < C.card)
    (s : Agent n G → Bool)
    (hedg : ∀ e : G.edgeSet, act (vcNet G k₀ k₁) 1 (Agent.edg e) s = true)
    (hkap : act (vcNet G k₀ k₁) 0 Agent.kap s = false) :
    (n : ℝ) / 2 * (qtil (999 / 1000) - qtil (998 / 1000)) <
      logBelief (vcNet G k₀ k₁) 2 Agent.iAg s := by sorry

end BayesGroupHard.VertexCover
