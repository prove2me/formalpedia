-- Prove2me | Theorems.Thm_BayesGroupHard_VertexCover_theorem_6
-- name    : BayesGroupHard.VertexCover.theorem_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:18:47.532614+00:00
-- url     : https://prove2.me/theorems/ca1c4636-7837-4dc2-aaff-07e7b8c67f99
-- title:
--   Theorem 6, p. 27 — small vertex covers force $\mu_{i,2}(1) < e^{-\Omega(n)}$, only large covers force $\mu_{i,2}(0) < e^{-\Omega(n)}$
-- statement:
--   This is the unconditional core of the paper's hardness theorem (Theorem 1, restated as Theorem 6).
--
--   There are constants $c > 0$ and $N$ such that the following holds for every $n \ge N$ and every simple graph $G$ on $n$ vertices. Build the vertex-cover network of $G$ ($n + m + 2$ agents), with agent $\kappa$'s signal structure $0 < \mathbb P_{\kappa,0}(0), \mathbb P_{\kappa,1}(0) < 1$ chosen so that
--   $$\lambda_\kappa(0) = \log\frac{\mathbb P_{\kappa,1}(0)}{\mathbb P_{\kappa,0}(0)} = -\frac n2\bigl(\tilde q(0.998) + \tilde q(0.999)\bigr).$$
--   Let $s$ be any signal profile on which agent $i$ observes the reduction's history: all edge agents announce $a_{\varepsilon,1} = 1$ and $\kappa$ announces $a_{\kappa,0} = 0$. Then the belief of $i$ at time two satisfies:
--
--   1. if $G$ has a vertex cover of size at most $0.85n$, then $\mu_{i,2}(1) < e^{-cn}$;
--   2. if all vertex covers of $G$ have size at least $0.999n$, then $\mu_{i,2}(0) < e^{-cn}$.
--
--   Combined with the NP-hardness of distinguishing these two kinds of graphs (Khot, Minzer and Safra's Theorem 5), this shows that computing a Bayesian agent's action at time two is NP-hard.
--
--   **Formalization Note.** $\exp(-\Omega(n))$ is rendered as $\exists c > 0, \exists N, \forall n \ge N$, with $c$ and $N$ chosen before the graph and before $\kappa$'s parameters, which depend on $n$. The belief is the model's posterior `post` on agent $i$'s information set at time $2$, for every profile on which the model's own actions produce the history; on all such profiles the information set is the same. The complexity clauses of Theorem 6 (a polynomial-time reduction, efficiently computable signal structures satisfying (9)) and the NP-hardness itself are not formalized. Here $n$ is the number of vertices of $G$, not the number of agents.
-- source:
--   Hązła, Jadbabaie, Mossel & Rahimian, Bayesian Decision Making in Groups is Hard, arXiv:1705.04770v4, p. 27, Theorem 6 (belief clauses), restating Theorem 1, p. 9

import Mathlib
import Definitions.Def_BayesGroupHard_VertexCover_Model

open Finset

namespace BayesGroupHard.VertexCover

/-- Theorem 6, p. 27 (belief clauses): there are `c > 0` and `N` such that for every graph `G`
on `n ≥ N` vertices, every signal structure of `κ` with `λ_κ(0) = -(n/2)(q̃(0.998) + q̃(0.999))`,
and every signal profile with the history "`a_{ε,1} = 1` for all edge agents, `a_{κ,0} = 0`":
* if `G` has a vertex cover of size at most `0.85 n`, then `µ_{i,2}(1) < exp(-c n)`;
* if all vertex covers of `G` have size at least `0.999 n`, then `µ_{i,2}(0) < exp(-c n)`. -/
theorem theorem_6 :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k₀ k₁ : ℝ),
        0 < k₀ → k₀ < 1 → 0 < k₁ → k₁ < 1 → Real.log (k₁ / k₀) = lamKappa0 n →
        ∀ s : Agent n G → Bool,
          (∀ e : G.edgeSet, act (vcNet G k₀ k₁) 1 (Agent.edg e) s = true) →
          act (vcNet G k₀ k₁) 0 Agent.kap s = false →
          ((∃ C : Finset (Fin n), G.IsVertexCover (C : Set (Fin n)) ∧
              (C.card : ℝ) ≤ 85 / 100 * n) →
            post (vcNet G k₀ k₁) true (infoSet (vcNet G k₀ k₁) 2 Agent.iAg s) <
              Real.exp (-(c * n))) ∧
          ((∀ C : Finset (Fin n), G.IsVertexCover (C : Set (Fin n)) →
              999 / 1000 * (n : ℝ) ≤ C.card) →
            post (vcNet G k₀ k₁) false (infoSet (vcNet G k₀ k₁) 2 Agent.iAg s) <
              Real.exp (-(c * n))) := by sorry

end BayesGroupHard.VertexCover
