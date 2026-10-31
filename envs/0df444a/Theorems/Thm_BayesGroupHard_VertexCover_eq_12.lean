-- Prove2me | Theorems.Thm_BayesGroupHard_VertexCover_eq_12
-- name    : BayesGroupHard.VertexCover.eq_12
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:18:39.72785+00:00
-- url     : https://prove2.me/theorems/d9f5acac-5f4e-4bdf-9023-53063121ae66
-- title:
--   (12), p. 29 — agent i's time-two log-belief ratio is a ratio of sums over vertex covers plus $\lambda_\kappa(0)$
-- statement:
--   In the vertex-cover network of a graph $G$ on $n$ vertices, let $\kappa$'s signal structure satisfy $0 < k_1 < k_0 < 1$, where $k_\theta = \mathbb P_{\kappa,\theta}(0)$. Let $s$ be any signal profile on which agent $i$ observes the history of the reduction: every edge agent announces $a_{\varepsilon,1} = 1$ and $\kappa$ announces $a_{\kappa,0} = 0$. Writing $\hat\Xi$ for the set of vertex covers of $G$,
--   $$\phi_{i,2} = \log\frac{\sum_{\hat\Sigma \in \hat\Xi} \bar p^{|\hat\Sigma|}(1-\bar p)^{n - |\hat\Sigma|}}{\sum_{\hat\Sigma \in \hat\Xi} \underline p^{|\hat\Sigma|}(1-\underline p)^{n - |\hat\Sigma|}} + \lambda_\kappa(0), \qquad \lambda_\kappa(0) = \log\frac{\mathbb P_{\kappa,1}(0)}{\mathbb P_{\kappa,0}(0)},$$
--   with $\bar p = 0.4$ and $\underline p = 0.3$. The summands are $\mathbb P_1\{\Sigma = \hat\Sigma\} = \bar q(\alpha)^n$ and $\mathbb P_0\{\Sigma = \hat\Sigma\} = \underline q(\alpha)^n$ for $|\hat\Sigma| = \alpha n$ ((10), (11)).
--
--   The formula reduces agent $i$'s Bayesian computation to a weighted count of vertex covers; the YES/NO bounds (13) and (18) start from it.
--
--   **Formalization Note.** $\phi_{i,2}$ is the model's `logBelief (vcNet G k₀ k₁) 2 iAg s`, for every profile `s` on which the model's own actions produce the history. The hypothesis $k_1 < k_0$ is the paper's informative-signal convention of Example 1 for $\kappa$ ($\mathbb P_{\kappa,1}(1) > \mathbb P_{\kappa,0}(1)$), under which $a_{\kappa,0} = s_\kappa$; the paper uses it implicitly when it writes $\mathbb P_{\kappa,\theta}(0)$ in (12), and it holds for the value of $\lambda_\kappa(0)$ chosen on p. 29. Without it the formula is false (for $k_1 > k_0$, $\kappa$ announces $0$ exactly when $s_\kappa = 1$). The weights are written with natural-number exponents $|\hat\Sigma|$ and $n - |\hat\Sigma|$, which is $\bar q(\alpha)^n$ with $\alpha = |\hat\Sigma|/n$.
-- source:
--   Hązła, Jadbabaie, Mossel & Rahimian, Bayesian Decision Making in Groups is Hard, arXiv:1705.04770v4, p. 29, (12), with (10), (11) on p. 28

import Mathlib
import Definitions.Def_BayesGroupHard_VertexCover_Model

open Finset

namespace BayesGroupHard.VertexCover

open scoped Classical in
/-- (12), p. 29: on every signal profile with the history "all edge agents announce
`a_{ε,1} = 1` and `κ` announces `a_{κ,0} = 0`", agent `i`'s time-two log-belief ratio is the
log-ratio of the vertex-cover sums plus `λ_κ(0) = log(P_{κ,1}(0)/P_{κ,0}(0))`. -/
theorem eq_12 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k₀ k₁ : ℝ)
    (hk₀ : 0 < k₀) (hk₀' : k₀ < 1) (hk₁ : 0 < k₁) (hk₁' : k₁ < 1)
    (hκ : k₁ < k₀)
    (s : Agent n G → Bool)
    (hedg : ∀ e : G.edgeSet, act (vcNet G k₀ k₁) 1 (Agent.edg e) s = true)
    (hkap : act (vcNet G k₀ k₁) 0 Agent.kap s = false) :
    logBelief (vcNet G k₀ k₁) 2 Agent.iAg s =
      Real.log
          ((∑ C ∈ univ.filter (fun C : Finset (Fin n) => G.IsVertexCover (C : Set (Fin n))),
              (4 / 10 : ℝ) ^ C.card * (6 / 10 : ℝ) ^ (n - C.card)) /
            (∑ C ∈ univ.filter (fun C : Finset (Fin n) => G.IsVertexCover (C : Set (Fin n))),
              (3 / 10 : ℝ) ^ C.card * (7 / 10 : ℝ) ^ (n - C.card))) +
        Real.log (k₁ / k₀) := by sorry

end BayesGroupHard.VertexCover
